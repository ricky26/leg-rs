use std::{num, io, fmt, error, result, thread, str, net, borrow};
use std::sync::mpsc;
use std::io::{Read, Write};
use std::borrow::Borrow;

#[derive(Clone,Debug)]
pub enum Error {
    NotEnoughData { needed: usize },
    IncorrectChecksum { got: u8, expected: u8 },
    MissingStart,
    MissingEnd,
    ParseError,
    UnexpectedCharacter { chr: char },
}
pub type Result<T> = result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", error::Error::description(self))
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            &Error::NotEnoughData { needed: _ } => "not enough data",
            &Error::IncorrectChecksum { got: _, expected: _ } => "incorrect checksum",
            &Error::MissingStart => "missing start character",
            &Error::MissingEnd => "missing end character",
            &Error::ParseError => "parse error",
            &Error::UnexpectedCharacter { chr: _ } => "unexpected character",
        }
    }
}

impl From<num::ParseIntError> for Error {
    fn from(_src: num::ParseIntError) -> Error {
        Error::ParseError
    }
}

#[derive(Clone,Debug)]
pub struct Command<'a>(borrow::Cow<'a, str>);

impl<'a> Command<'a> {
    pub fn new(src: &'a str) -> Command<'a> {
        Command(borrow::Cow::Borrowed(src))
    }

    pub fn new_owned(src: String) -> Command<'static> {
        Command(borrow::Cow::Owned(src))
    }

    pub fn checksum_str(src: &str) -> u8 {
        let mut ret = 0u8;

        for i in src.bytes() {
            ret = ret.wrapping_add(i)
        }

        ret
    }

    pub fn contents(&self) -> &str {
        let contents: &str = self.0.borrow();
        contents
    }

    pub fn checksum(&self) -> u8 {
        Command::checksum_str(self.contents())
    }

    pub fn write<T: Write>(&self, out: &mut T) -> io::Result<()> {
        write!(out, "${}#{:02x}", self.contents(), self.checksum())
    }
    
    pub fn fmt<T: fmt::Write>(&self, out: &mut T) -> fmt::Result {
        write!(out, "${}#{:02x}", self.contents(), self.checksum())
    }

    pub fn to_owned(&self) -> Command<'static> {
        Command(borrow::Cow::Owned(self.contents().to_owned()))
    }
}

impl<'a> fmt::Display for Command<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.fmt(fmt)
    }
}

#[derive(Clone,Debug)]
pub enum Packet<'a> {
    Ack,
    Nack,
    Command(Command<'a>),
}

impl<'a> Packet<'a> {
    pub fn parse(src: &'a str) -> Result<(&'a str, Packet<'a>)> {
        if src.len() < 1 {
            return Err(Error::NotEnoughData { needed: 1 })
        }

        match src.chars().next() {
            Some('$') => {},
            Some('+') => return Ok((&src[1..], Packet::Ack)),
            Some('-') => return Ok((&src[1..], Packet::Nack)),
            Some(x) => return Err(Error::UnexpectedCharacter { chr: x }),
            _ => return Err(Error::ParseError),
        }

        if src.chars().next() != Some('$') {
            return Err(Error::MissingStart)
        }
        
        if src.len() < 4 {
            return Err(Error::NotEnoughData { needed: 4 })
        }

        let end = match src.find('#') {
            None => { return Err(Error::MissingEnd) },
            Some(x) => x,
        };

        if src.len() < end + 3 {
            return Err(Error::NotEnoughData { needed: end + 3 })
        }

        let contents = &src[1..end];
        let chksum_calc = Command::checksum_str(contents);
        let chksum_existing = try!(u8::from_str_radix(&src[end+1..end+3], 16));

        if chksum_calc != chksum_existing {
            return Err(Error::IncorrectChecksum { got: chksum_existing, expected: chksum_calc })
        }

        Ok((&src[end+3..], Packet::Command(Command(borrow::Cow::Borrowed(contents)))))
    }

    pub fn write<T: Write>(&self, out: &mut T) -> io::Result<()> {
        match self {
            &Packet::Ack => write!(out, "+"),
            &Packet::Nack => write!(out, "-"),
            &Packet::Command(ref x) => x.write(out),
        }
    }
    
    pub fn fmt<T: fmt::Write>(&self, out: &mut T) -> fmt::Result {
        match self {
            &Packet::Ack => write!(out, "+"),
            &Packet::Nack => write!(out, "-"),
            &Packet::Command(ref x) => x.fmt(out),
        }
    }

    pub fn to_owned(&self) -> Packet<'static> {
        match self {
            &Packet::Ack => Packet::Ack,
            &Packet::Nack => Packet::Nack,
            &Packet::Command(ref x) => {
                Packet::Command(Command(borrow::Cow::Owned(x.contents().to_owned())))
            },
        }
    }
}

impl<'a> fmt::Display for Packet<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.fmt(fmt)
    }
}

enum ServerCommand {
    ClientReady(net::TcpStream),
    ClientDisconnected,
    Packet(Packet<'static>),
}
pub struct Server {
    receiver: Option<mpsc::Receiver<ServerCommand>>,
    stream: Option<net::TcpStream>,
    to_send: Vec<u8>,
    no_ack: bool,

    last_response: Command<'static>,
}

impl Server {
    pub fn new() -> Server {
        Server {
            receiver: None,
            stream: None,
            to_send: Vec::new(),
            no_ack: false,

            last_response: Command::new(""),
        }
    }

    pub fn start_listening<T: net::ToSocketAddrs + Send + 'static>(&mut self, bind_to: T) {
        let (send, recv) = mpsc::channel();
        self.receiver = Some(recv);
        
        thread::spawn(move || {
            let listener = net::TcpListener::bind(bind_to).unwrap();
            
            for stream in listener.incoming() {
                let mut stream = stream.unwrap();
                send.send(ServerCommand::ClientReady(stream.try_clone().unwrap())).unwrap();

                let mut vec = Vec::new();
                let mut buf = [0u8;1024];
                while let Ok(amt) = stream.read(&mut buf) {
                    vec.write_all(&buf[0..amt]).unwrap();
                    let mut done = 0;

                    loop {
                        let string = str::from_utf8(&vec[done..]).unwrap();
                        let ret = Packet::parse(string);
                        match ret {
                            Ok((new_slice, cmd)) => {
                                send.send(ServerCommand::Packet(cmd.to_owned())).unwrap();
                                done += vec.len() - new_slice.len();
                            },
                            _=> break,
                        }
                    }

                    vec = Vec::from(&vec[done..vec.len()]);
                }

                send.send(ServerCommand::ClientDisconnected).unwrap();
            }
        });
    }
    
    pub fn send_command(&mut self, cmd: &Command) {
        self.last_response = cmd.to_owned();
        self.send_packet(&Packet::Command(cmd.clone()))
    }

    pub fn send_packet(&mut self, cmd: &Packet) {
        //println!("<<< {}", cmd);
        if let Err(_) = match self.stream.as_mut() {
            Some(x) => cmd.write(x),
            None => cmd.write(&mut self.to_send),
        } {
            cmd.write(&mut self.to_send).ok();
        }
    }

    pub fn process_commands<T: for<'a> FnMut(&'a Command<'a>)>(&mut self, mut callback: T) {
        while let Ok(command) = self.receiver.as_mut().map_or(Err(mpsc::TryRecvError::Empty), |x| x.try_recv()) {
            match command {
                ServerCommand::ClientReady(stream) => {
                    let mut stream = stream;
                    stream.write(&self.to_send[..]).ok();
                    self.stream = Some(stream);
                    self.to_send.clear()
                },
                ServerCommand::ClientDisconnected => {
                    self.stream = None;
                    self.no_ack = false;
                },
                ServerCommand::Packet(src) => {
                    //println!(">>> {}", &src);
                    
                    match &src {
                        &Packet::Ack => {},
                        &Packet::Nack => {
                            let packet = &Packet::Command(self.last_response.clone());
                            self.send_packet(packet);
                        },

                        &Packet::Command(ref x) => {
                            if !self.no_ack {
                                self.send_packet(&Packet::Ack);
                            }

                            if regex!("qSupported.*").is_match(x.contents()) {
                                self.send_command(&Command::new("QStartNoAckMode+;PacketSize=1023"));
                            } else if x.contents() == "QStartNoAckMode" {
                                self.no_ack = true;
                                self.send_command(&Command::new("OK"));
                            } else {
                                callback(x);
                            }
                        },
                    }
                },
                
            }
        }
    }
}

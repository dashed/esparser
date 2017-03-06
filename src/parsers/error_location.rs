// local imports

use super::current_position::CurrentPosition;

// structs

#[derive(Debug)]
pub struct ErrorLocation {
    location: CurrentPosition,
    description: String,
}

impl ErrorLocation {
    pub fn new(location: CurrentPosition, description: String) -> Self {
        ErrorLocation {
            location: location,
            description: description,
        }
    }
}

impl ::std::error::Error for ErrorLocation {
    fn description(&self) -> &str {
        &self.description
    }
}

impl ::std::fmt::Display for ErrorLocation {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        write!(f,
               "Line {}, Column {}: {}",
               self.location.line(),
               self.location.col(),
               self.description)
    }
}

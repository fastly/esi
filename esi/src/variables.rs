use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(String),
    Error(String),
    Null,
}

impl Value {
    pub fn to_bool(&self) -> bool {
        match self {
            Value::String(_) => true,
            Value::Error(_) => false,
            Value::Null => false,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Value::String(s) => s.clone(),
            Value::Error(_) => "".to_string(),
            Value::Null => "".to_string(),
        }
    }
}

pub struct Variables {
    map: HashMap<String, Value>,
}

impl Variables {
    pub fn new() -> Variables {
        Variables {
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: String, value: Value) {
        match value {
            Value::Null => {}
            _ => {
                self.map.insert(name, value);
            }
        };
    }

    pub fn get(&self, name: &str) -> &Value {
        self.map.get(name).unwrap_or(&Value::Null)
    }
}

impl<const N: usize> From<[(String, Value); N]> for Variables {
    fn from(data: [(String, Value); N]) -> Variables {
        Variables {
            map: HashMap::from(data),
        }
    }
}

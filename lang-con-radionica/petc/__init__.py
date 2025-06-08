
import tatsu 

syntax = """


@@grammar::PetC

start = statements:statements  $;

identifier = /[A-Za-z_][A-Za-z_0-9]*/ ;
number = /[0-9]+\\.?[0-9]*/ ;
string = /\"[^\"]*\"/ ;



op_plus = "+" ;
op_minus = "-" ;
op_multiply = "*" ;
op_divide = "/" ;

op_assign = "=" ;

relop_less = "<" ;
relop_greater = ">" ;
relop_less_equal = "<=" ;
relop_greater_equal = ">=" ;
relop_equal = "==" ;
relop_not_equal = "!=" ;

open_paren = "(" ;
close_paren = ")" ;
true = "true" ;
false = "false" ;
null = "null" ;



constant = string | number | true | false | null ;

expression = left:term op:op_plus right:expression | left:term op:op_minus right:expression | left:term;
term = left:factor op:op_multiply right:term | left:factor op:op_divide right:term | left:factor;
factor = value:value | open_paren expression:expression close_paren | function_call:function_call  | identifier:identifier ;
function_call = name:identifier open_paren args:arguments close_paren  | name:identifier open_paren close_paren ;
value = number | string | "true" | "false" | "null";
arguments = head:expression tail:arguments | head:expression ;

statements = head:statement tail:statements | head:statement ;

statement = expression:expression ";" | assignment:assignment ";" ;
assignment = identifier:identifier op:op_assign expression:expression ;
"""


EXAMPLE = """
a = 3;
b = 4;
c = a + b;
print(c);

"""
import re 

def contains(ast, value):
    return hasattr(ast, value) and getattr(ast, value) is not None

class Parser:

    def __init__(self):
        self.symbols = {}
    

    def start(self, ast):
        return ast.statements
    def statements(self, ast):
        if not contains(ast, 'tail') or not ast.tail:
            return [ast.head]
        return [ast.head] + ast.tail if hasattr(ast, 'tail') else [ast.head]
    
    def statement(self, ast):
        if contains(ast, 'expression'):
            return lambda s: ast.expression(s)
        elif contains(ast, 'assignment'):
            return lambda s: ast.assignment(s)
        else:
            raise ValueError("Unknown statement type %s" % ast)
        
    def assignment(self, ast):
        if ast.op == '=':
            return lambda s: s.update({ast.identifier: ast.expression(s)})
        else:
            raise ValueError(f"Unknown assignment operator: {ast.op}")

    def expression(self, ast):
        if contains(ast, 'left') and contains(ast, 'op') and hasattr(ast, 'right'):
            return lambda s: ast.op(ast.left(s), ast.right(s))
        else:
            return lambda s: ast.left(s)
    
    def term(self, ast):
        if contains(ast, 'left') and contains(ast, 'op') and hasattr(ast, 'right'):
            return lambda s: ast.op(ast.left(s), ast.right(s))
        else:
            return lambda s: ast.left(s)
        
    def factor(self, ast):
        if contains(ast, 'identifier'):
            return lambda s: s.get(ast.identifier, None)
        elif contains(ast, 'value'):
            return lambda s: ast.value
        elif contains(ast, 'function_call'):
            return lambda s: ast.function_call(s)
        elif contains(ast, 'expression'):
            return lambda s: ast.expression(s)
        else:
            raise ValueError("Unknown factor type")
        
    def function_call(self, ast):
        def f(s):
            name = ast.name
            args = [arg(s) for arg in ast.args] if contains(ast, 'args') else []
            if name in s:
                return s[name](*args)
            else:
                raise ValueError(f"Function {name} is not defined")
        return f

    def arguments(self, ast):
        return [ast.head] if not contains(ast, "tail") else [ast.head] + ast.tail

    def value(self, ast):
        if isinstance(ast, str):
            return ast
        elif isinstance(ast, (int, float)):
            return ast
        elif ast == 'true':
            return True
        elif ast == 'false':
            return False
        elif ast == 'null':
            return None
        else:
            raise ValueError(f"Unknown value type: {ast}")
        
    def identifier(self, ast):
        return ast
    
    def number(self, ast):
        return float(ast) if '.' in ast else int(ast)
    
    def string(self, ast):
        return ast.string.strip('"')
    
    def op_plus(self, ast):
        return lambda x, y: x + y
    def op_minus(self, ast):
        return lambda x, y: x - y
    def op_multiply(self, ast):
        return lambda x, y: x * y
    def op_divide(self, ast):
        return lambda x, y: x / y if y != 0 else ValueError("Division by zero")
    
    def op_assign(self, ast):
        return '='
    
    def relop_less(self, ast):
        return lambda x, y: x < y
    def relop_greater(self, ast):
        return lambda x, y: x > y
    def relop_less_equal(self, ast):
        return lambda x, y: x <= y
    def relop_greater_equal(self, ast):
        return lambda x, y: x >= y
    def relop_equal(self, ast):
        return lambda x, y: x == y
    def relop_not_equal(self, ast):
        return lambda x, y: x != y
    

    

# Zadatak: Implementirati type checking pre izvršavanja programa
# Na primer, svi izrazi mogu biti objekti koji imaju metodu __call__ koja se može pozvati da se evaluiraju izrazi ali pored toga postoji i metoda check(symbols) koja proverava da li su svi izrazi ispravni pre izvršavanja programa.

class Expression:
    def __call__(self, symbols):
        raise NotImplementedError("Subclasses should implement this method")
    
    def check(self, symbols):
        return None  # Placeholder for type checking logic
    
class Plus(Expression):

    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __call__(self, symbols):
        return lambda x, y: x + y
    
    def check(self, symbols):
        args_valid = self.left.check(symbols) and self.right.check(symbols) 
        left_type = self.left.check(symbols)
        right_type = self.right.check(symbols)
        if left_type != right_type:
            return None 
        return left_type

parser = tatsu.compile(syntax, semantics=Parser())

def parse(text):
    # remove comments 
    text = re.sub(r'#.*', '', text)
    return parser.parse(text)

def check_types(ast):
    return True # Placeholder for type checking logic

def run(text):
    parsed = parse(text)
    if not check_types(parsed):
        raise ValueError("Type checking failed")
    statements = parsed 
    symbols = {
        "print": print
    }
    for statement in statements:
        if callable(statement):
            statement(symbols)
        else:
            raise ValueError(f"Statement {statement} is not callable")
    return symbols


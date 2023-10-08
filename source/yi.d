import std.algorithm;
import std.array;
import std.conv;
import std.exception;
import std.meta;
import std.regex;
import std.stdio;
import std.string;
import std.sumtype;

import std.meta : AliasSeq, Repeat;
import std.typecons : Tuple, tuple;
import std.algorithm : map;
import std.conv : to;
import std.string : split;
import std.range : isInputRange, ElementType;

auto tuplify(size_t n, R)(R r) if (isInputRange!R) {
   Tuple!(Repeat!(n, ElementType!R)) result;

   static foreach (i; 0..n) {
      result[i] = r.front;
      r.popFront();
   }
   assert(r.empty);

   return result;
}



// class LispD {

static {

alias   TypeError = Exception;
alias LookupError = Exception;
alias SyntaxError = Exception;

// single field struct / class, alias
// so Array can be shared! not the D's plain array (as fat pointer!) which is value type
// Array's element type is the *struct* type Value! so scalar types are directly there, no need for another indirection
class  Array  { Value[] values; alias values this; }
static assert(is(Array == class));
static assert(Array.sizeof == 8);

/*
struct Bool   { bool    value; alias value this; }
struct Int    { long    value; alias value this; }
struct Double { double  value; alias value this; }
struct Obj    { Object  value; alias value this; }  // D object on the heap
struct List   { Array   value; alias value this; }  // List is actually a *thin* pointer to an Array object
*/

// except string literal, all build-in keywords, user function and variable names are all symbols
static class String {  // wrapper of string
 public:
  this(string s) {value = s;}
  string value;
  override string toString() {return value;}
}
alias Symbol = String;
static Symbol[string] symbol_table;
static assert(Symbol.sizeof == 8);


// alias Value = SumType!(Bool, Int, Double, List, Obj, Symbol);
enum : ubyte {BOOL, INT, DOUBLE, OBJECT, ARRAY, STRING, SYMBOL, PROC}
struct Value {  // tagged union! TODO: shall we just use boxed class type Int Double String?
  ubyte tag;
  union {
    bool   bVal;
    long   iVal;
    double dVal;

    Object obj;  // D lang object
    Array  arr;
    String str;
    Symbol sym;
    Procedure proc;  // callable
  }
}

// alias Bool(value) = Value(BOOL, value);

static assert(is(Value == struct));
static assert(Value.sizeof == 16);  // each Value is 2x size of a pointer

alias Cell = Value*;  // always return pointer, so (set! (car list) val) work for scalar type (Int ...)
static assert(Cell.sizeof == 8);

static Symbol Sym(string s) {
  //"Find or create unique Symbol entry for str s in symbol table."
  if (s !in symbol_table) {
    symbol_table[s] = new Symbol(s);
  }
  return symbol_table[s];
}


static immutable Value  TRUE_VAL = Value(BOOL, true);
static immutable Value FALSE_VAL = Value(BOOL, false);
static immutable Cell TRUE  =  &TRUE_VAL;
static immutable Cell FALSE = &FALSE_VAL;

static
void initList(ref Cell result) {
  result.tag = ARRAY;
  result.arr = new Array();       // copy the struct List into Value, the array itself is on the heap
}

static
Cell newList(Value[] items) {
  Cell result = new Value(ARRAY);  // on the heap
  initList(result);
  result.arr.values = items;  // only copy the struct fat pointer itself
  return result;
}

static
Cell newList(Cell[] items=null) {  // TODO: is this version correct?
  Cell result = new Value(ARRAY);  // on the heap
  initList(result);
  foreach (ref item; items) {
    result.arr.values ~= *item;  // TODO(doc): is the struct copy semantics right?
  }
  return result;
}

static
Cell newSymbol(Symbol sym) {
  // TODO: cache same sym
  Cell result = new Value(SYMBOL);  // on the heap
  result.sym  = sym;
  return result;
}

static
Cell newString(string str) {
  // TODO: cache same sym
  Cell result = new Value(STRING);  // on the heap
  result.str  = new String(str);
  return result;
}
// CellT: so `immutable Cell` can work as just `Cell`, in this func the item is struct copied anyway, so it does not matter
Cell appendList(CellT)(Cell list, CellT item) {
  if (ARRAY == list.tag) {
    list.arr ~= *item;  // append a copy of the struct *item
  }
  return list;
}

long length(Cell list) {
  long result = -1;
  if (ARRAY == list.tag) {
    result = list.arr.length;
  }
  return result;
}

Cell car(Cell list) {
  Cell result = null;

  if (ARRAY == list.tag) {
    result = &(list[0]);
  };
  return result;
}

unittest {
	/+
  Cell list = newList();
  assert(list.length == 0);
  assert("()" == to_string(list));

  appendList(list, TRUE);
  assert(list.length == 1);

  appendList(list, FALSE);
  assert(list.length == 2);

  assert("(true false)" == to_string(list));

  Cell expr = newList();
  appendList(expr, list);
  appendList(expr, list);
  writeln(to_string(expr));

  Cell head = expr.car.car;
  writeln(to_string(list));
  *head = *list;  // NOTE: here we created cycle in the expr tree!
  /*
  writeln(to_string(list));
  writeln(to_string(head));
  writeln(to_string(expr));
  */
  +/
}


alias symbolize = std.algorithm.iteration.map!(s => Sym(s)); // std.meta.staticMap

static
Symbol    _quote, _if, _set, _define, _lambda, _begin, _definemacro, _macroexpand;

Symbol    _quasiquote, _unquote, _unquotesplicing;
Symbol    _append, _cons, _let;

void init() {
AliasSeq!(_quote, _if, _set, _define, _lambda, _begin, _definemacro, _macroexpand) = symbolize(
          "quote   if   set!  define   lambda   begin   define-macro  macroexpand".split()).tuplify!8;
AliasSeq!(_quasiquote, _unquote, _unquotesplicing) = symbolize(
          "quasiquote   unquote   unquote-splicing".split()).tuplify!3;
AliasSeq!(_append, _cons, _let) = symbolize(
          "append   cons   let".split()).tuplify!3;
}



class Procedure {
    // "A user-defined Scheme procedure.", including macro!
    Env env;
    Symbol[] parms;  // array of params
    Cell exp;

    this(Cell parms, Cell exp, Env env) {
      enforce(parms.tag == ARRAY);
      foreach (parm; parms.arr) {
        enforce(parm.tag == SYMBOL);
        this.parms ~= parm.sym;
      }
	this.exp   = exp;
	this.env   = env;
    }

    Cell opCall(Cell args) {
      // flatten args
      enforce(args.tag == ARRAY);
      enforce(args.arr.length == parms.length);  // no partial call for now
      Cell[] vals;
      foreach (ref arg; args.arr) {
        vals ~= &arg;
      }
      return eval(this.exp, new Env(this.parms, vals, this.env));  // *new* scope for the call, funcall cost
    }
}

Cell newProcedure(Procedure proc) {
  // TODO: cache same sym
  Cell result = new Value(PROC);  // on the heap
  result.proc = proc;
  return result;
}

// ################ parse, read, and user interaction
class StringIO {
  string buf;
  long cursor;
  this(string buf) { this.buf = buf; }

  string readln(dchar terminator = '\n') {  // The line that was read, including the line terminator character.
    long end = std.string.indexOf(buf, terminator, cursor);
    string line = null;  // eof
    if (end != -1) {
      line = buf[cursor .. ++end];
      cursor = end;
    }
    return line;
  }
}

Cell parse(string inport) {
    // "Parse a program: read and expand/error-check it."
    // # Backwards compatibility: given a str, convert it to an InPort
    return parse!(InPort!StringIO)(new InPort!StringIO(new StringIO(inport)));
}

Cell parse(InPortT)(InPortT inport) {
    return expand(read(inport), true);
}

static Symbol eof_object;

// FileT: can be std.stdio.File, or StringIO, or std.stdio.stdin
class InPort(FileT) {
    // "An input port. Retains a line of chars."
    immutable auto tokenizer = std.regex.ctRegex!(`\s*(,@|[('` ~ "`" ~ `,)]|"(?:[\\].|[^\\"])*"|;.*|[^\s('"` ~ "`" ~ `,;)]*)(.*)`);
    string line;
    FileT file;
    this(FileT file) {
        this.file = file;
    }
    string next_token() {
        // "Return the next token, reading new text into line buffer if needed."
        while (true) {
            if (this.line == "") this.line = this.file.readln();  // first try to read next line
            if (this.line == "") return null;  // eof_object
	    auto m = matchFirst(this.line, tokenizer);
            string token = m[1];  // m[0] is the full match
	    this.line = m[2];
            if (token != "" && !token.startsWith(';')) {
                return token;
            }
	}
     }
}
/*
char readchar(InPort inport) {
    // "Read the next character from an input port."
    if (inport.line != "") {
        char ch = inport.line[0];
	inport.line = inport.line[1 .. $];
        return ch;
    } else {
        return inport.file.read(1) || eof_object;
    }
}
*/
Cell read(InPortT)(InPortT inport) {
    // "Read a Scheme expression from an input port."
    void read_ahead(string token, Cell collector) {
        if ("(" == token) {
            initList(collector);
            while (true) {
                token = inport.next_token();
                if (token == ")") return;
                else {
                  Cell result = new Value();  // heap allocated
		  read_ahead(token, result);
		  appendList(collector, result);
		}
	    }
	}
	else if (")" == token)     { throw new SyntaxError("unexpected )"); }
        else if (token is null)    { throw new SyntaxError("unexpected EOF in list"); }
        else if (token in quotes)  { // => (quote exp)
	  initList(collector);
	  appendList(collector, newSymbol(quotes[token]));
	  appendList(collector, read(inport)); }
        else { *collector = atom(token); }  // copy the struct!
    }

    // # body of read:
    Cell result;  // = eof_object;
    string token1 = inport.next_token();
    if (token1 !is null) {
      result = new Value();  // heap allocated
      read_ahead(token1, result);
    }
    return result;
}
static Symbol[string] quotes;

// just return Value here, we do NOT want to do heap allocation
Value atom(string token) {
    // 'Numbers become numbers; #t and #f are booleans; "..." string; otherwise Symbol.'
    Value val;
    if      (token == "#t") return  TRUE_VAL;
    else if (token == "#f") return FALSE_VAL;
    else if (token[0] == '"') {val.tag = STRING; val.str = new String(token[1 .. $-1]);}  // TODO: .encode("utf-8").decode("unicode-escape");
    else if (std.string.isNumeric(token)) {
      if (canFind(token, '.')) {
        val.tag = DOUBLE;  val.dVal = token.to!double;
      } else {
        val.tag = INT;     val.iVal = token.to!long;
      }
    } else {
      // try: return complex(token.replace('i', 'j', 1))
      val.tag = SYMBOL;
      val.sym = Sym(token);
    }
  return val;
}


static string to_string(ref Value x) {
    // "Convert a Python object back into a Lisp-readable string."
  string result;
  switch (x.tag) {
    case BOOL  : result = x.bVal.to!string;  break;
    case INT   : result = x.iVal.to!string;  break;
    case DOUBLE: result = x.dVal.to!string;  break;
    case OBJECT: result = x.obj .to!string;  break;
    case SYMBOL: result = x.sym .to!string;  break;
    case ARRAY : result = "(" ~ join(map!to_string(x.arr.values), " ") ~ ")";  break;

    /*
    else if(isa(x, str): return '"%s"' % x.encode('unicode-escape').decode("utf8").replace('"',r'\"')
    else if(isa(x, complex): return str(x).replace('j', 'i')
    */
    default: enforce(false);
  }
  // writeln(result);
  return result;
}

static string to_string(Cell x) {
  return to_string(*x);
}


void load(string filename) {
    // "Eval every expression from a file."
    repl(null, new InPort!File(File(filename)));
}
void repl(FileT)(string prompt, FileT inport, File outs=stdout) {
    // "A prompt-read-eval-print loop."
    stdout.write("Lispy version 2.0\n");
    while (true) {
        try {
            if (prompt) stdout.write(prompt);
            Cell x = parse(inport);
            if (x is null) return;
            Cell val = eval(x);
            if (val !is null /*&& outs*/) outs.writeln(to_string(val));
	} catch (Exception e) {
            outs.writeln(e);
	}
    }
}
// ################ Environment class
static string to_string(Symbol[] args) { return join(map!(x => x.toString)   (args), " "); }
static string to_string(  Cell[] args) { return join(map!(x =>  to_string(x))(args), " "); }

static class Env {
    // "An environment: a dict of {'var':val} pairs, with an outer Env."
    Env outer;
    Cell[Symbol] dict;

    this(Symbol parms=null, Cell args=null, Env outer=null) {
        // # Bind parm list to corresponding args, or single parm to list of args
        this.outer = outer;
	// assert(typeid(args) == typeid(List));
        this.dict[parms] = args;
    }

    this(Symbol[] parms, Cell[] args, Env outer=null) {
        this.outer = outer;
            if (args.length != parms.length)
                throw new TypeError(format("expected %s, given %s, ", to_string(parms), to_string(args)));
	    foreach (i; 0 .. parms.length) { this.dict[parms[i]] = args[i]; }
    }

    Env find(Symbol var) {
        // "Find the innermost Env where var appears."
        if (var in this.dict) return this;
	else if (this.outer is null)  {throw new LookupError(var.value);}
        else return this.outer.find(var);
    }
}
bool is_pair(Cell x) {return x.arr.length == 2 && (x.tag == ARRAY);}
Cell[] cons(Cell x, Cell y)  {return [x, y];}
/+
def callcc(proc):
    "Call proc with current continuation; escape only"
    ball = RuntimeWarning("Sorry, can't continue this continuation any longer.")
    def throw(retval): ball.retval = retval; throw ball
    try:
        return proc(throw);
    except RuntimeWarning as w:
        if w is ball: return ball.retval
        else: throw w
+/
static Env add_globals(Env self) {
    // "Add some Scheme standard procedures."
/*
    import math, cmath, operator as op;
    self.update(vars(math))
    self.update(vars(cmath))
    self.update({
     '+':op.add, '-':op.sub, '*':op.mul, '/':op.truediv, 'not':op.not_, 
     '>':op.gt, '<':op.lt, '>=':op.ge, '<=':op.le, '=':op.eq, 
     'equal?':op.eq, 'eq?':op.is_, 'length':len, 'cons':cons,
     'car': (x => &(x.values[0])), 'cdr':lambda x:x[1:], 'append':op.add,  
     'list':lambda *x:list(x), 'list?': lambda x:isa(x,list),
     'null?':lambda x:x==[], 'symbol?':lambda x: isa(x, Symbol),
     'boolean?':lambda x: isa(x, bool), 'pair?':is_pair, 
     'port?': lambda x:isa(x,file), 'apply':lambda proc,l: proc(*l), 
     'eval':lambda x: eval(expand(x)), 'load':lambda fn: load(fn), 'call/cc':callcc,
     'open-input-file':open,'close-input-port':lambda p: p.file.close(), 
     'open-output-file':lambda f:open(f,'w'), 'close-output-port':lambda p: p.close(),
     'eof-object?':lambda x:x is eof_object, 'read-char':readchar,
     'read':read, 'write':lambda x,port=sys.stdout:port.write(to_string(x)),
     'display':lambda x,port=sys.stdout:port.write(x if isa(x,str) else to_string(x))})
     */
    return self;
}
// isa = isinstance;

Env global_env;

static this() {
eof_object = new Symbol("#<eof-object>");  // # Note: uninterned; can't be read

global_env = add_globals(new Env());
}


// ################ eval (tail recursive)

static
Cell eval(Cell x, Env env=global_env) {
    // "Evaluate an expression in an environment."
    while (true) {
      if (x.tag == SYMBOL) {
        return env.find(x.sym).dict[x.sym];  // variable reference
      } else if (x.tag != ARRAY) {  // (!isa(x, list))   // constant literal
        return x;
      } else {
        Symbol head = x.arr[0].sym;
        if (head is _quote) {   // (quote exp)
            Cell exp = &(x.arr[1]);
            return exp;
	} else if(head is _if) {      // (if test conseq alt)
            // (_, test, conseq, alt) = x;
            x = &(eval(&(x.arr[1]), env) ? x.arr[2]: x.arr[3]);
        } else if(head is _set) {     // (set! var exp)
            // (_, var, exp) = x;
	    enforce(x[2].tag == ARRAY);  // must be a ARRAY
            Symbol var = x[1].sym;
	    Cell exp = &(x[2]);
            env.find(var).dict[var] = eval(exp, env);
            return null;
        } else if(head is _define) {  // (define var exp)
            // (_, var, exp) = x;
	    enforce(x[2].tag == ARRAY);  // must be a ARRAY
            Symbol var = x[1].sym;
	    Cell exp = &(x[2]);  // .arr
            env.dict[var] = eval(exp, env);
            return null;
        } else if(head is _lambda) {  // (lambda (var*) exp)
            // (_, vars, exp) = x;
	    enforce(x[1].tag == ARRAY);  // must be a ARRAY
	    enforce(x[2].tag == ARRAY);  // must be a ARRAY
            Cell vars = &(x[1]);
	    Cell exp  = &(x[2]);
            return newProcedure(new Procedure(vars, exp, env));  // NOTE: this return need to be a Cell type!
        } else if(head is _begin) {   // (begin exp+)
            foreach (exp; x.arr[1 .. $-1])
                eval(&exp, env);
            x = &(x.arr[$-1]);           // NOTE: x will be eval-ed (and return) in the while loop's next itr
        } else {                   // (proc exp*)
            Cell[] exps;
	    foreach (exp; x.arr) exps ~= eval(&exp, env);
            Cell proc = exps[0];  exps.popFront();
            if (typeid(proc) == typeid(Procedure)) {  // user defined lisp Procedure
                Procedure prc = cast(Procedure)proc;
                x = prc.exp;
                env = new Env(prc.parms, exps, prc.env);  // NOTE: will continue the while loop to eval with proc.env as outer env! *new* scope for the call, funcall cost
	    } else {
                // TODO: return proc(exps); // native buildin or foreign D-func
                writeln("native call:", to_string(proc), to_string(exps));
		return null;
	    }
	}
      }
    }
}
// ################ expand

static Cell expand(ref Value x, bool toplevel=false) {
  return expand(&x, toplevel);
}

static Cell expand(Cell x, bool toplevel=false) {
  // "Walk tree of x, making optimizations/fixes, and signaling SyntaxError."
  require(x, x.arr.values != []);                    // () => Error
  if (x.tag != ARRAY) {                 // constant => unchanged
      return x;
  } else {
    Symbol head = x.arr[0].sym;
    if (head is _quote) {                 // (quote exp)
        require(x, x.arr.length==2);
        return x;
    } else if(head is _if) {                    
        if (x.arr.length==3) appendList(x, newList());     // (if t c) => (if t c null)
        require(x, x.arr.length==4);
        return newList(map!expand(x.arr.values).array);
    } else if(head is _set) {                   
        require(x, x.arr.length==3); 
        Cell var = &(x.arr[1]);                       // (set! non-var exp) => Error
        require(x, (var.tag == SYMBOL), "can set! only a symbol");
        return newList([newSymbol(_set), var, expand(&(x.arr[2]))]);
    } else if(head is _macroexpand) {
        require(x, x.arr.length==2);            // (macroexpand exp)
        return newList([newSymbol(Sym("display")), newString(to_string(expand(&(x[1]))))]);  // *compile* to: display this code string!
    } else if(head is _define || head is _definemacro) {
        require(x, x.arr.length>=3);
        Symbol _def = head;
	Cell v = &(x.arr[1]);
	Value[] body = x.arr[2 .. $];
        if ((v.tag == ARRAY) && v) {           // (define (f args) body)
            Cell f = &(v.arr[0]);
	    Value[] args = v.arr[1 .. $];        //  => (define f (lambda (args) body))
            return expand(newList([newSymbol(_def), f, newList([newSymbol(_lambda), newList(args), newList(body)])]));
	} else {
            require(x, x.arr.length==3);        // (define non-var/list exp) => Error
            require(x, (v.tag == SYMBOL), "can define only a symbol");
            Cell exp = expand(&(x.arr[2]));
            if (_def is _definemacro) {     
                require(x, toplevel, "define-macro only allowed at top level");
                Cell proc = eval(exp);         // NOTE: because this eval! will be done in global_env (in this expand() we do not have another env); and here we call the eval (runtime) in compile time on the code itself (as data)!
                require(x, (typeid(proc) == typeid(Procedure)), "macro must be a procedure");
                macro_table[v.sym] = proc.proc;    // (define-macro v proc)
                return null;              //  => null; add v:proc to macro_table
	    }
            return newList([newSymbol(_define), v, exp]);
	}
    } else if(head is _begin) {
        if (x.arr.length==1)  return null;        // (begin) => null
        else {
	    Cell result = newList();
	    foreach (xi; x.arr) appendList(result, expand(&xi, toplevel));
	    return result;
	}
    } else if(head is _lambda) {                // (lambda (x) e1 e2) 
        require(x, x.arr.length>=3);            //  => (lambda (x) (begin e1 e2))
        Cell vars = &(x.arr[1]);
	Value[] body = x.arr[2 .. $];
	if (!(vars.tag == SYMBOL))
        foreach (v; vars.arr) require(x, ((vars.tag == ARRAY) && ((v.tag == SYMBOL) )
                ), "illegal lambda argument list");
        Cell exp = (body.length == 1) ? &(body[0]) : newList([*newSymbol(_begin)] ~ body);
        return newList([newSymbol(_lambda), vars, expand(exp)]);
    } else if(head is _quasiquote) {            // `x => expand_quasiquote(x)
        require(x, x.arr.length==2);
        return expand_quasiquote(&(x.arr[1]));
    } else if((x.arr[0].tag == SYMBOL) && head in macro_table) {  // => macroexpand if m isa macro
        return expand(macro_table[head](newList(x.arr[1 .. $])), toplevel); // (m arg...) 
    } else {
        return newList(map!expand(x.arr.values).array);            // (f arg...) => expand each
    }
  }
}

static void require(Cell x, bool predicate, string msg="wrong length") {
    // "Signal a syntax error if predicate is false."
    if (!predicate) throw new SyntaxError(to_string(x)~": "~msg);
}

Cell expand_quasiquote(Cell x) {
    // """Expand `x => 'x; `,x => x; """
    if (!is_pair(x))
        return newList([newSymbol(_quote), x]);
    require(x, x[0].sym !is _unquotesplicing, "can't splice here");
    if (x.arr[0].sym is _unquote) {
        require(x, x.arr.length==2);
        return &(x.arr[1]);
    } else if(is_pair(&(x.arr[0])) && x.arr[0].arr[0].sym is _unquotesplicing) {  //  `(,@x y) => (append x y)
        require(&(x[0]), (x.arr[0].arr.length)==2);
        return newList([newSymbol(_append), &(x.arr[0].arr[1]), expand_quasiquote(newList(x.arr[1 .. $]))]);
    } else
        return newList([newSymbol(_cons), expand_quasiquote(&(x.arr[0])), expand_quasiquote(newList(x.arr[1 .. $]))]);
}
/* TODO: define in lisp?
Procedure let(Cell args ...) {
    args = list(args);
    Cell x = cons(_let, args);
    require(x, len(args)>1);
    bindings, body = args[0], args[1 .. $];
    foreach (b; bindings) require(x, (isa(b, list) && len(b)==2 && isa(b[0], Symbol)
                   ), "illegal binding list");
    vars, vals = list(zip(*bindings));
    return [[_lambda, list(vars)]+list(map(expand, body))] + list(map(expand, vals));
}
*/
Procedure[Symbol] macro_table;  // = [/*_let:let*/];  // ## More macros can go here
}


  // ctor
void this_ctor() {
  init();
quotes = ["'":_quote, "`":_quasiquote, ",":_unquote, ",@":_unquotesplicing];
/*
eval(parse(r"(begin

(define-macro and (lambda args 
   (if (null? args) #t
       (if (= (length args) 1) (car args)
           `(if ,(car args) (and ,@(cdr args)) #f)))))

;; More macros can also go here

)"));
*/
}

// }

void yi_main() {
  // auto lispD = new LispD();
  this_ctor();
  // lispD.
  repl("lispy> ", new InPort!(typeof(stdin))(stdin));
}


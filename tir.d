import rational;
import codepage;

import std.ascii;
import std.algorithm.comparison;
import std.algorithm.iteration;
import std.algorithm.mutation;
import std.algorithm.searching;
import std.algorithm.setops;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.functional;
import std.range;
import std.stdio;
import std.string;
import std.typecons;
import std.utf;
import core.vararg;

string readBytes(string fileName) {
    return to!string(fileName.read);
}

T[] digits(T)(T n) {
    T[] res;
    if(n == 0) res ~= cast(T)(0);
    while(n != 0) {
        res = n % cast(T)(10) ~ res;
        n /= cast(T)(10);
    }
    return res;
}

T[] range(T)(T min, T max) {
    T[] res;
    for(T i = min; i <= max; i++) {
        res ~= i;
    }
    return res;
}

T[] range(T)(T max) {
    return BigInt(0).range(max - 1);
}

string asCapitalized(string s) {
    if(s.length <= 1) return s.toUpper;
    return s[0..1].toUpper ~ s[1..$].toLower;
}

// https://stackoverflow.com/a/33055496/4119004
class ExitException : Exception {
    int returnCode;

    @safe pure nothrow this(int returnCode, string file = __FILE__, size_t line = __LINE__) {
        super(null, file, line);
        this.returnCode = returnCode;
    }
}

class TirError : Exception {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }

    static void raise(Tir inst, string message) {
        throw new TirTypeError(
            "[" ~ to!string(inst.ip) ~ "]: TirError: " ~ message
        );
    }
}

class TirTypeError : TirError {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }

    static void raise(string name, Tir inst, Element[] els) {
        string sig = els.map!("to!string(a.type)")
                        .array
                        .join(", ");

        TirError.raise(inst,
            name ~ " cannot be called with argument signature: " ~
            sig ~ "\nStack:" ~
            inst.stack.map!(a => "    " ~ to!string(a)).join("\n")
        );
    }
}

class IndexingError : Exception {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

void times(T)(T n, void delegate() fn) {
    for(T i = 0; i < n; i++) fn();
}
void times(BigInt n, void delegate() fn) {
    for(BigInt i = 0; i < n; i++) fn();
}

string[] mapstring(T)(T arr) {
    return arr.map!(to!string).array;
}

T pop(T)(ref T[] arr) {
    T last = arr[$ - 1];
    arr.length--;
    return last;
}
void push(T)(ref T[] arr, T el) {
    arr ~= el;
}

enum TokenType {
    number, string, implicitString, command, meta, func_start, func_end, set_var, set_func,
    whitespace, quote_n, comment, none
}

string toString(TokenType type) {
    return to!string(type);
}

class Token {
    string raw;
    TokenType type;
    size_t start;

    this() {
        this("", TokenType.none, 0);
    }

    this(string raw, TokenType type, size_t start) {
        this.raw = raw;
        this.type = type;
        this.start = start;
    }

    string codeform() {
        if(type == TokenType.meta && raw[$-1] == '{') {
            return raw[0..$-1];
        }
        else {
            return raw;
        }
    }

    override string toString() {
        return format("Token(%s, %s, %s)", raw, type.toString(), start);
    }
}

class Tokenizer {
    protected size_t ptr = 0;
    protected dchar[] code;
    protected Token[] tokens = [];
    protected dchar[] metas;

    TokenType[dchar] translations;

    this(string code) {
        this(code, []);
    }

    this(string code, dchar[] metas) {
        this.code = code.byDchar.array;
        this.metas = metas;
        translations = [
            '{': TokenType.func_start,
            '}': TokenType.func_end
        ];
    }

    dchar cur() {
        return code[ptr];
    }

    void advance() {
        advance(1);
    }
    void advance(int n) {
        ptr += n;
    }

    bool hasLeft() {
        return ptr < code.length;
    }

    void readRun(ref string str, bool delegate(dchar) validate) {
        while(hasLeft && validate(cur)) {
            str ~= cur;
            advance;
        }
    }

    string readRun(bool delegate(dchar) validate) {
        string res = "";
        readRun(res, validate);
        return res;
    }

    bool isMeta(dchar c) {
        return metas.map!(e => e == c).any;
    }

    bool isMeta() {
        return isMeta(cur);
    }

    void step() {
        Token next = new Token();
        next.start = ptr;
        long implicitIndex = code.indexOf('⦀', ptr);
        if(implicitIndex != -1) {
            next.type = TokenType.implicitString;
            while(ptr <= implicitIndex) {
                next.raw ~= cur;
                advance;
            }
        }
        else if(cur.isDigit) {
            next.type = TokenType.number;
            readRun(next.raw, (&isDigit).toDelegate());
        }
        else if(cur.isWhite) {
            next.type = TokenType.whitespace;
            readRun(next.raw, (&isWhite).toDelegate());
        }
        else if(isMeta) {
            next.type = TokenType.meta;
            readRun(next.raw, &isMeta);
            if(hasLeft) {
                next.raw ~= cur;
                if(cur != '{') {
                    advance;
                }
            }
            else {
                next.raw ~= '0';
            }
            // next.raw ~= cur;
            // advance;
        }
        // quote string «...»
        else if(cur == '«') {
            int depth = 0;
            do {
                if(cur == '«') {
                    depth++;
                }
                else if(cur == '»') {
                    depth--;
                }
                next.raw ~= cur;
                advance;
            } while(depth);
            next.type = TokenType.string;
        }
        else if(cur in translations) {
            next.type = translations[cur];
            next.raw ~= cur;
            advance;
        }
        else if(cur == ':') {
            next.type = TokenType.set_var;
            next.raw ~= cur;
            advance;
            next.raw ~= cur;
            advance;
        }
        else if(cur == ';') {
            next.type = TokenType.set_func;
            next.raw ~= cur;
            advance;
            next.raw ~= cur;
            advance;
        }
        // https://www.unicode.org/charts/nameslist/n_2460.html
        else if(cur >= '①' && cur <= '⑳') {
            int rep = cur - '①' + 2;
            next.type = TokenType.quote_n;
            rep.times(delegate void() {
                next.raw ~= cur;
                advance;
            });
        }
        else if(cur == '⫽') {
            next.type = TokenType.comment;
            while(hasLeft && cur != '\n') {
                next.raw ~= cur;
                advance;
            }
        }
        else {
            next.type = TokenType.command;
            next.raw ~= cur;
            advance;
        }

        tokens ~= next;
    }

    Token[] run() {
        while(hasLeft) {
            step;
        }
        return tokens;
    }
}

Token[] tokenize(string str) {
    Tokenizer inst = new Tokenizer(str);
    return inst.run;
}

Token[] tokenize(string str, dchar[] metas) {
    Tokenizer inst = new Tokenizer(str, metas);
    return inst.run;
}

enum ElementType {
    number, string, array, func, rational, any,
    arrayLike
}
union ElementValue {
    BigInt num;
    string str;
    Element[] arr;
    voidTir fun;
    Rational rat;
}

class Element {
    ElementValue value;
    ElementType type;
    string funcRepr;

    this(voidTir fun, string repr) {
        update(fun, repr);
    }
    this(int n) {
        this(BigInt(n));
    }
    this(double n) {
        this(Rational(n));
    }
    this(T)(T el) {
        update(el);
    }
    this(T, S)(T t, S s) {
        update(t, s);
    }

    static Element opCall(T)(T el) {
        return new Element(el);
    }
    static Element opCall(T, S)(T t, S s) {
        return new Element(t, s);
    }

    void update(Element el) {
        type = el.type;
        value = el.value;
        funcRepr = el.funcRepr;
    }
    void update(string str) {
        type = ElementType.string;
        value.str = str;
    }
    void update(BigInt num) {
        type = ElementType.number;
        value.num = num;
    }
    void update(Element[] arr) {
        type = ElementType.array;
        value.arr = arr;
    }
    void update(Rational rat) {
        type = ElementType.rational;
        value.rat = rat;
    }
    void update(voidTir fun) {
        update(fun, "<no representation>");
    }
    void update(voidTir fun, string repr) {
        type = ElementType.func;
        value.fun = fun;
        funcRepr = repr;
    }

    bool truthy() {
        switch(type) {
            case ElementType.array:
                return true;
            case ElementType.string:
                return value.str.length != 0;
            case ElementType.number:
                return value.num != 0;
            case ElementType.rational:
                return value.rat != 0;
            case ElementType.func:
                return true;

            default:
                assert(0);
        }
    }

    override string toString() {
        switch(type) {
            case ElementType.array:
                return to!string(value.arr);
            case ElementType.string:
                return value.str;
            case ElementType.number:
                return to!string(value.num);
            case ElementType.rational:
                return to!string(value.rat);
            case ElementType.func:
                return funcRepr;

            default:
                assert(0);
        }
    }

    string repr() {
        switch(type) {
            case ElementType.array:
                return "[" ~ value.arr.map!("a.repr").join(", ") ~ "]";
            case ElementType.string:
                return "«" ~ value.str ~ "»";
            case ElementType.number:
                return to!string(value.num);
            case ElementType.rational:
                return to!string(value.rat);
            case ElementType.func:
                return funcRepr;

            default:
                assert(0);
        }
    }

    Element castTo(ElementType castType) {
        if(castType == type) return Element(this);

        switch(castType) {
            // to a string
            case ElementType.string:
                switch(type) {
                    case ElementType.number, ElementType.rational, ElementType.func:
                        return Element(toString);

                    case ElementType.array:
                        return Element(value.arr.map!(to!string).join);

                    default:
                        assert(0, "undefined cast from " ~ to!string(type) ~ " to " ~ to!string(castType) ~ "!");
                }

            // to an array
            case ElementType.array:
                switch(type) {
                    case ElementType.string:
                        return Element(value.str.byDchar.map!(a => Element(to!string(a))).array);

                    case ElementType.number:
                        return Element(value.num.digits.map!(Element).array);

                    default:
                        assert(0, "undefined cast from " ~ to!string(type) ~ " to " ~ to!string(castType) ~ "!");
                }

            // to a number
            case ElementType.number:
                switch(type) {
                    case ElementType.string:
                        return Element(BigInt(value.str));

                    case ElementType.array:
                        BigInt[] digits = value.arr.map!(a => a.castTo(ElementType.number).value.num).array;
                        BigInt res = 0;
                        foreach(digit; digits) {
                            res *= 10;
                            res += digit;
                        }
                        return Element(res);

                    default:
                        assert(0, "undefined cast from " ~ to!string(type) ~ " to " ~ to!string(castType) ~ "!");
                }

            default:
                assert(0, "no castTo cases are defined for type <" ~ to!string(castType) ~ ">!");
        }
    }

    Element[] toArray() {
        return castTo(ElementType.array).value.arr;
    }

    override bool opEquals(Object other) {
        if(typeid(other) == typeid(Element)) {
            return opEquals(cast(Element)other);
        }
        return false;
    }

    bool opEquals(Element other) {
        if(other.type != type) {
            return false;
        }
        switch(type) {
            case ElementType.number:
                return value.num == other.value.num;

            case ElementType.string:
                return value.str == other.value.str;

            case ElementType.array:
                if(value.arr.length != other.value.arr.length) {
                    return false;
                }
                return zip(value.arr, other.value.arr).all!"a[0] == a[1]";

            default:
                assert(0, "No opEquals defined for two <" ~ to!string(type) ~ ">");
        }
    }

    static signature oneFunc = [ElementType.func];
    static signature oneRational = [ElementType.rational];
    static signature oneArray = [ElementType.array];
    static signature oneNumber = [ElementType.number];
    static signature oneString = [ElementType.string];
    static signature anyOne = [ElementType.any];

    static signature twoNumbers = [ElementType.number, ElementType.number];
    static signature twoArrays = [ElementType.array, ElementType.array];
    static signature twoStrings = [ElementType.string, ElementType.string];
    static signature anyTwo = [ElementType.any, ElementType.any];

    static multiElement idFunction() {
        return delegate Element(Tir inst, signature sig, Element[] args) {
            return args[0];
        };
    }

    static signature anyN(size_t n) {
        return cycle([ElementType.any]).take(n).array;
    }
}

alias voidTir = void delegate(Tir);
alias metaTir = voidTir delegate(Tir, string, voidTir);
alias signature = ElementType[];
alias signatureAction = void delegate(Tir, ref Element[], ref signature);

bool signatureEqual(signature as, signature bs) {
    if(as.length != bs.length) {
        return false;
    }

    foreach(a, b; lockstep(as, bs)) {
        if(a != ElementType.any && b != ElementType.any) {
            if(b == ElementType.arrayLike && a.among!(ElementType.string, ElementType.array)) {
                continue;
            }
            if(a != b) {
                return false;
            }
        }
    }

    return true;
}

voidTir unary(Element delegate(Tir, Element) fn) {
    return delegate void(Tir inst) {
        Element[] els;
        signature sig;
        assert(inst.matchSignature(Element.anyOne, sig, els));
        inst.push(fn(inst, els[0]));
    };
}

voidTir binary(string name, Element delegate(Tir, signature, Element, Element) fn) {
    return caseFunction(name, [
        matcher(Element.anyTwo, delegate Element(Tir inst, signature sig, Element[] args) {
            return fn(inst, sig, args[0], args[1]);
        })
    ]);
}

alias multiElement = Element delegate(Tir, signature, Element[]);
alias matcher = Tuple!(signature, "match", multiElement, "fn");

voidTir caseFunction(string name, matcher[] cases) {
    return delegate void(Tir inst) {
        Element[] els;
        signature sig;

        foreach(m; cases) {
            if(inst.matchSignature(m.match, sig, els)) {
                Element res = m.fn(inst, sig, els);
                inst.push(res);
                return;
            }
        }

        assert(inst.matchSignature(Element.anyOne, sig, els));
        TirTypeError.raise(name, inst, els);
    };
}

class Consumer(T) {
    size_t pos = 0;
    T[] possible;
    T otherwise;

    this(T o) {
        otherwise = o;
    }
    this(T[] p) {
        possible = p;
    }
    this(T[] p, T o) {
        otherwise = o;
        possible = p;
    }

    void append(T el) {
        possible ~= el;
    }

    T consume() {
        /* writeln("Consuming @ ", pos, ";", possible.length, ";", otherwise); */
        if(pos < possible.length)
            return possible[pos++];
        else
            return otherwise;
    }
}

bool isPrime(BigInt a) {
    if(a.among(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)) {
        return true;
    }
    else if(a % 2 == 0 || a % 3 == 0 || a % 5 == 0
    || a % 7 == 0 || a % 11 == 0 || a % 13 == 0) {
        return false;
    }
    for(BigInt i = 17; i <= a.isqrt; i += 6) {
        if (a % i == 0 || a % (i + 2) == 0) return false;
    }
    return true;
}

T[] rotateLeft(T, K)(T[] arr, K n = 1) {
    n.times(delegate void() {
        arr = arr[$-1] ~ arr[0..$-1];
    });
    return arr;
}
T[] rotateRight(T, K)(T[] arr, K n = 1) {
    n.times(delegate void() {
        arr = arr[1..$] ~ arr[0];
    });
    return arr;
}
T[] rotate(T, K)(T[] arr, K n = 1) {
    if(n < 0) return rotateRight(arr, -n);
    else      return rotateLeft(arr, n);
}

Element[] vectorize(Tir inst, voidTir fn, Element[] as, Element[] bs) {
    size_t maxSize = max(as.length, bs.length);
    Element[] res;
    Element a, b;
    foreach(i; 0..maxSize) {
        a = as[i % as.length];
        b = bs[i % bs.length];
        res ~= inst.callOp(fn, a, b);
    }
    return res;
}

// vaguely based off of https://stackoverflow.com/a/11962756/4119004
BigInt isqrt(BigInt x) {
    if(x == BigInt(0) || x == BigInt(1)) {
        return x;
    }
    BigInt i;
    for(i = x / 2; i > x / i; i = (x / i + i) / 2) {}
    return i;
}

class Tir {
    static string preamble = "Ao:CBo:D";
    Element[] stack = [];
    Token[] tokens;
    size_t ip = 0;
    voidTir[dchar] ops;
    metaTir[dchar] meta;
    Element[dchar] vars;
    Consumer!Element arguments;

    // actions
    signatureAction beforeCall = null;


    this(string code) {
        Tir.assignOps(this);
        Tir.assignVars(this);
        checkCodepage;
        runAsChild(preamble);
        tokens = code.tokenize(meta.keys);
    }

    this(Token[] code) {
        tokens = code;
    }

    this(Token[] code, Tir inst) {
        this(code);
        inherit(inst);
    }

    void checkCodepage() {
        auto combined = ops.keys ~ meta.keys;
        auto diff = combined.filter!(a => !tirCodepage.canFind(a));
        assert(diff.array.length == 0, diff.mapstring.join ~ " <-- you forgot those");
    }

    Element pop() {
        if(stack.length) {
            return stack.pop;
        }
        else {
            return arguments.consume;
            /* return new Element(BigInt("0")); */
        }
    }
    void push(Element el) {
        if(el is null) return;
        stack.push(el);
    }
    void push(T)(T el) {
        push(new Element(el));
    }
    void push(int el) {
        push(BigInt(el));
    }
    void push(bool el) {
        push(el ? 1 : 0);
    }
    void push(BigInt el) {
        stack ~= new Element(el);
    }
    void pushMulti(Element[] args...) {
        foreach(el; args)
            push(el);
    }

    signature signatureof(T...)(T args) {
        return args.map!(e => e.type).array;
    }

    signature pop2(out Element a, out Element b) {
        b = pop;
        a = pop;
        return signatureof([a, b]);
    }

    signature popN(size_t n, out Element[] els) {
        els = [];
        els.length = n;
        size_t offset = 0;
        bool unset = true;
        for(size_t i = n - 1; i < n; --i) {
            if(stack.length) {
                els[i] = pop;
            }
            else {
                if(unset) {
                    offset = i;
                    unset = false;
                }
                els[offset - i] = pop;
            }
        }
        return signatureof(els);
    }
    Element[] popN(size_t n) {
        Element[] res;
        popN(n, res);
        return res;
    }

    void needs(size_t n) {
        auto test = popN(n);
        pushMulti(test);
    }

    signature peekN(size_t n, out Element[] els) {
        els = [];
        els.length = n;
        for(size_t i = n - 1; i < n; --i) {
            /* writefln("n,i: %s,%s", n, i); */
            // detect underflow
            if(stack.length - n + i > stack.length) {
                throw new IndexingError("peekN tried to peek more elements than in the stack!");
            }
            els[i] = stack[$ - n + i];
        }
        return signatureof(els);
    }

    bool matchSignature(signature search, out signature result, out Element[] els) {
        size_t n = search.length;
        needs(n);
        Element[] e;
        signature sig;
        try {
            sig = peekN(n, e);
        } catch(IndexingError err) {
            return false;
        }
        if(sig.signatureEqual(search)) {
            popN(n, els);
            if(beforeCall) {
                // writeln("ACTIVATING BEFORE CALL!");
                beforeCall(this, els, sig);
                beforeCall = null;
            }
            result = sig;
            return true;
        }
        return false;
    }

    void assignSignature(signature sig, Element[] els, ...) {
        for(size_t i = 0; i < els.length; i++) {
            auto type = _arguments[i];
            if(type == typeid(Element*)) {
                Element* e = va_arg!(Element*)(_argptr);
                *e = els[i];
            }
            else if(type == typeid(BigInt*)) {
                BigInt* k = va_arg!(BigInt*)(_argptr);
                *k = els[i].value.num;
            }
            else if(type == typeid(string*)) {
                string* s = va_arg!(string*)(_argptr);
                *s = els[i].value.str;
            }
            else if(type == typeid(Element[]*)) {
                Element[]* a = va_arg!(Element[]*)(_argptr);
                *a = els[i].toArray;
            }
            else if(type == typeid(voidTir*)) {
                voidTir* f = va_arg!(voidTir*)(_argptr);
                *f = els[i].value.fun;
            }
            else {
                stderr.writeln("Unhandled type " ~ to!string(type) ~ " in assignSignature");
            }
        }
    }

    void inherit(Tir inst) {
        ops = inst.ops;
        meta = inst.meta;
        stack = inst.stack;
        vars = inst.vars;
        arguments = inst.arguments;
    }

    void callOp(voidTir fn, ref Element[] outStack, Element[] args...) {
        auto oldStack = stack;
        stack = args;
        fn(this);
        outStack = stack;
        stack = oldStack;
    }

    void callOp(dchar c, ref Element[] outStack, Element[] args...) {
        callOp(ops[c], outStack, args);
    }

    Element callOp(T)(T fn, Element[] args...) {
        Element[] temp;
        callOp(fn, temp, args);
        return temp.pop;
    }

    void advance() {
        ip++;
    }

    void runAsChild(T)(T input, Element[] args...) {
        pushMulti(args);
        runAsChild(input);
    }

    void runAsChild(Token[] tokens) {
        Tir subInst = new Tir(tokens, this);
        subInst.run;
        inherit(subInst);
    }

    void runAsChild(string code) {
        Token[] tokens = code.tokenize(meta.keys);
        runAsChild(tokens);
    }

    voidTir readFunc(ref string source) {
        Token cur = tokens[ip];
        Token[] inner = [];
        int depth = 0;
        source = "";

        assert(cur.type == TokenType.func_start);

        do {
            if(cur.type == TokenType.func_end) {
                depth--;
            }
            else if(cur.type == TokenType.func_start) {
                depth++;
            }

            source ~= cur.codeform;
            inner ~= cur;

            ip++;
            if(ip >= tokens.length)
                break;

            cur = tokens[ip];
        } while(depth);
        ip--;

        inner = inner[1..$-1];

        return delegate void(Tir inst) {
            inst.runAsChild(inner);
        };
    }

    voidTir readFunc() {
        string temp;
        return readFunc(temp);
    }

    void debugStack() {
        writeln("== stack debug ==");
        foreach(i, el; stack.enumerate) {
            writefln("stack[%s] = %s", i, el.repr);
        }
    }

    void step() {
        Token cur = tokens[ip];
        // writeln(vars);
        if(cur.raw.length >= 1 && cur.raw[0] in vars) {
            push(vars[cur.raw[0]]);
        }
        else switch(cur.type) {
            case TokenType.number:
                push(BigInt(cur.raw));
                break;
            // do nothing
            case TokenType.whitespace:
                break;

            case TokenType.command:
                dchar key = cur.raw.byDchar.array[0];
                if(key in ops) {
                    auto fn = ops[key];
                    fn(this);
                }
                else {
                    stderr.writeln("Undefined operator `" ~ cur.raw ~ "`");
                }
                break;

            case TokenType.meta:
                dchar[] chars = cur.raw.byDchar.array;
                assert(chars.length >= 2);
                dchar[] keys = chars[0..$-1];
                dchar target = chars[$-1];

                string source = cur.codeform;
                /* writeln("keys ", keys);
                writefln("Meta of %s under %s", target, keys); */
                voidTir fn;
                if(target == '.') {
                    Element top = pop;
                    assert(top.type == ElementType.func);
                    fn = top.value.fun;
                }
                else if(target in ops) {
                    fn = ops[target];
                }
                else if(target.isDigit) {
                    BigInt n = BigInt(to!string(target));
                    fn = delegate void(Tir inst) {
                        inst.push(n);
                    };
                }
                else if(target == '{') {
                    advance;
                    string append;
                    fn = readFunc(append);
                    source ~= append;
                }
                else {
                    stderr.writefln("Undefined operator `%s` passed to meta `%s`", target, keys);
                    break;
                }
                foreach_reverse(key; keys) {
                    fn = meta[key](this, source, fn);
                }
                fn(this);
                break;

            case TokenType.func_start:
                // collect tokens
                string source;
                push(new Element(readFunc(source), source));

                break;

            case TokenType.string:
                push(
                    cur.codeform.byDchar
                       .mapstring
                       .array[1..$-1]
                       .join
                );
                break;

            case TokenType.implicitString:
                push(
                    cur.codeform.byDchar
                       .mapstring
                       .array[0..$-1]
                       .join
                );
                break;

            case TokenType.set_var:
                vars[cur.raw[1]] = pop;
                break;

            case TokenType.set_func:
                Element top = pop;
                assert(top.type == ElementType.func);
                ops[cur.raw[1]] = top.value.fun;
                break;

            case TokenType.quote_n:
                push(cur.raw.byDchar.array[1..$].mapstring.join);
                break;

            case TokenType.comment:
                break;

            default:
                stderr.writefln("Unhandled type %s", cur.type);
                assert(0);
        }

        advance;
    }

    void run() {
        while(ip < tokens.length) {
            step;
        }
    }

    void setVar(dchar key, Element[] els) {
        vars[key] = new Element(els);
    }
    void setVar(T)(dchar key, T el) {
        vars[key] = new Element(el);
    }

    void aliasFunc(dchar id, string code) {
        Token[] tokens = code.tokenize(meta.keys);
        ops[id] = delegate void(Tir inst) {
            inst.runAsChild(tokens);
        };
    }

    // uppercase values reserved for variables
    static void assignVars(Tir base) {
        base.setVar('A', "ABCDEFGHIJKLMNOPQRSTUVWXYZ");
        base.setVar('B', "abcdefghijklmnopqrstuvwxyz");
        base.setVar('E', "");
        base.setVar('F', false);
        base.setVar('N', "\n");
        base.setVar('M', "\t");
        base.setVar('S', " ");
        base.setVar('T', true);
        base.setVar('Y', []);
    }

    static void assignOps(Tir base) {
        // iota
        base.ops['ι'] = caseFunction("ι (Iota)", [
            matcher(Element.oneNumber, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a;
                inst.assignSignature(sig, args, &a);
                return Element(a.range.map!(Element).array);
            })
        ]);
        // sqrt
        base.ops['√'] = caseFunction("√ (SquareRoot)", [
            matcher(Element.oneNumber, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a;
                inst.assignSignature(sig, args, &a);
                return Element(a.isqrt);
            })
        ]);
        // input
        base.ops['i'] = delegate void(Tir inst) {
            inst.push(inst.arguments.consume);
        };
        // type cast
        base.ops['t'] = caseFunction("t (TypeCast)", [
            matcher(Element.anyTwo, delegate Element(Tir inst, signature sig, Element[] args) {
                Element first, like;
                inst.assignSignature(sig, args, &first, &like);
                return first.castTo(like.type);
            })
        ]);
        // meta: type cast
        base.meta['∷'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return caseFunction("∷ (TypeCastMeta)", [
                matcher(Element.anyOne, delegate Element(Tir inst, signature sig, Element[] args) {
                    Element source;
                    inst.assignSignature(sig, args, &source);

                    Element res = inst.callOp(fn, source);
                    assert(res.type == ElementType.number, "expected a number in TypeCastMeta");

                    int type = to!int(res.value.num);

                    return source.castTo(to!ElementType(type));
                })
            ]);
        };
        base.ops['='] = caseFunction("= (Equal)", [
            matcher(Element.anyTwo, delegate Element(Tir inst, signature sig, Element[] args) {
                return Element(args[0] == args[1]);
            })
        ]);
        base.aliasFunc('≠', "=¬");
        // call/negate
        base.ops['~'] = caseFunction("~ (Negate)", [
            matcher(Element.oneFunc, delegate Element(Tir inst, signature sig, Element[] args) {
                voidTir fn;
                inst.assignSignature(sig, args, &fn);
                fn(inst);
                return null;
            }),
            matcher(Element.oneNumber, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt n;
                inst.assignSignature(sig, args, &n);
                return Element(-n);
            })
        ]);
        base.ops['&'] = caseFunction("& (Concat)", [
            matcher(Element.anyTwo, delegate Element(Tir inst, signature sig, Element[] args) {
                Element[][] multiArray = args.map!(delegate Element[](Element el) {
                    if(el.type == ElementType.array)
                        return el.value.arr;
                    else
                        return [el];
                }).array;
                return Element(join(multiArray));
            })
        ]);
        // exit
        base.ops['.'] = delegate void(Tir inst) {
            throw new ExitException(0);
        };
        // string representation
        base.ops['℘'] = unary(delegate Element(Tir inst, Element el) {
            return Element(el.repr);
        });
        // rotate right N times
        base.ops['⤏'] = caseFunction("⤏ (RotateLeft)", [
            matcher([ElementType.arrayLike, ElementType.number], delegate Element(Tir inst, signature sig, Element[] args) {
                Element[] arr;
                BigInt n;
                inst.assignSignature(sig, args, &arr, &n);
                return Element(arr.rotate(n)).castTo(args[0].type);
            })
        ]);
        // rotate left N times
        base.aliasFunc('⤎', "~⤏");
        // rotate right once
        base.aliasFunc('⤍', "1⤏");
        // rotate left once
        base.aliasFunc('⤌', "1⤎");
        // meta: capitalize
        // 0 - uppercase
        // 1 - lowercase
        // 2 - swapcase
        // 3 - asCapitalized
        // 4 - title case
        // 5 - uppercase first character
        // 6 - lowercase first character
        base.meta['c'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return caseFunction(source ~ " (MetaCapitalize)", [
                matcher(Element.oneString, delegate Element(Tir inst, signature sig, Element[] args) {
                    string s;
                    inst.assignSignature(sig, args, &s);

                    Element[] temp;
                    inst.callOp(fn, temp, args[0]);
                    Element res = temp.pop;
                    /* writeln("res =", res); */
                    assert(res.type == ElementType.number);
                    int type = to!int(res.value.num);

                    switch(type) {
                        case 0:
                            return Element(s.toUpper);

                        case 1:
                            return Element(s.toLower);

                        case 2:
                            goto default;

                        case 3:
                            return Element(s.asCapitalized);

                        case 4:
                            return Element(s.split(" ").map!(asCapitalized).join(" "));

                        case 5:
                            if(s.length <= 1) return Element(s.toUpper);
                            return Element(s[0..1].toUpper ~ s[1..$]);

                        case 6:
                            if(s.length <= 1) return Element(s.toLower);
                            return Element(s[0..1].toLower ~ s[1..$]);

                        default:
                            stderr.writeln("Unsupported method to `c`: ", type);
                    }
                    return Element(0);
                })
            ]);
        };
        // range
        base.ops['r'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;

            if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                inst.assignSignature(sig, els, &a, &b);
                Element[] res;
                for(BigInt i = a; i < b; i++) {
                    res ~= new Element(i);
                }
                inst.push(res);
            }
            else {
                writeln("no ops");
            }
        };
        // bidirectional inclusive range
        base.ops['∠'] = caseFunction("∠ (BidirectionalRange)", [
            matcher(Element.twoNumbers, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a, b;
                inst.assignSignature(sig, args, &a, &b);
                int dir = 2 * to!int(a < b) - 1;
                Element[] res;
                for(BigInt i = a; i != b + dir; i += dir) {
                    res ~= Element(i);
                }
                return Element(res);
            })
        ]);
        // multiplication
        base.ops['×'] = caseFunction("× (Multiply)", [
            matcher(Element.oneArray, delegate Element(Tir inst, signature sig, Element[] args) {
                inst.runAsChild("⤚×", args[0]);
                return null;
            }),
            matcher(Element.twoNumbers, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a, b;
                inst.assignSignature(sig, args, &a, &b);
                return Element(a + b);
            }),
        ]);
        // divide
        base.ops['÷'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                inst.assignSignature(sig, els, &a, &b);
                inst.push(a / b);
            }
        };
        // pair
        base.ops[','] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyTwo, sig, els));
            Element a, b;
            inst.assignSignature(sig, els, &a, &b);
            inst.push([a, b]);
        };
        // is truthy
        base.ops['⊨'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyOne, sig, els));
            Element top = els[0];
            inst.push(top.truthy);
        };
        // print/output single entity
        base.ops['⨞'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyOne, sig, els));
            writeln(els[0]);
        };
        // print without popping
        base.ops['⟁'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyOne, sig, els));
            writeln(els[0]);
            inst.push(els[0]);
        };
        // ord
        base.ops['o'] = caseFunction("o (OrdinalOf)", [
            matcher(Element.oneString, delegate Element(Tir inst, signature sig, Element[] args) {
                return Element(to!int(args[0].toArray[0].value.str[0]));
            }),
            matcher(Element.oneNumber, Element.idFunction)
        ]);
        // convert to function
        base.ops['⨐'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.oneString, sig, els));
            string s = els[0].value.str;
            voidTir fn = delegate void(Tir inst) {
                inst.runAsChild(s);
            };
            inst.push(new Element(fn, "{" ~ s ~ "}"));
        };
        // join array
        base.ops['⨝'] = caseFunction("⨝ (Join)", [
            matcher(Element.oneArray, delegate Element(Tir inst, signature sig, Element[] args) {
                Element[] arr;
                inst.assignSignature(sig, args, &arr);
                return Element(arr.mapstring.join);
            }),
            matcher([ElementType.array, ElementType.any], delegate Element(Tir inst, signature sig, Element[] args) {
                Element[] arr;
                Element joiner;
                inst.assignSignature(sig, args, &arr, &joiner);
                return Element(arr.mapstring.join(to!string(joiner)));
            }),
        ]);
        // split string
        base.ops['⟠'] = caseFunction("⟠ (Split)", [
            matcher(Element.twoStrings, delegate Element(Tir inst, signature sig, Element[] args) {
                string target, splitter;
                inst.assignSignature(sig, args, &target, &splitter);
                string[] sections = target.split(splitter);
                return Element(sections.map!(Element).array);
            }),
            matcher(Element.oneString, delegate Element(Tir inst, signature sig, Element[] args) {
                string target;
                inst.assignSignature(sig, args, &target);
                string[] sections = target.split("");
                return Element(sections.map!(Element).array);
            }),
        ]);
        // logical negation
        base.ops['¬'] = unary(delegate Element(Tir inst, Element el) {
            return new Element(!el.truthy);
        });
        // grid/ungrid
        base.ops['g'] = caseFunction("g (GridUnGrid)", [
            matcher(Element.oneArray, delegate Element(Tir inst, signature sig, Element[] args) {
                inst.push(args[0]);
                inst.runAsChild("#⨝N⨝");
                return null;
            })
        ]);
        // assign to G
        base.ops['⅁'] = unary(delegate Element(Tir inst, Element el) {
            inst.vars['G'] = el;
            return el;
        });
        // assign to Y
        base.ops['⅄'] = unary(delegate Element(Tir inst, Element el) {
            inst.vars['Y'] = el;
            return el;
        });
        // assign to L (peek)
        base.ops['⅂'] = unary(delegate Element(Tir inst, Element el) {
            inst.vars['L'] = el;
            return el;
        });
        // assign to L (pop)
        base.ops['⅂'] = unary(delegate Element(Tir inst, Element el) {
            inst.vars['L'] = el;
            return null;
        });
        // fraction/rational creation
        base.ops['∕'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.twoNumbers, sig, els));
            BigInt a, b;
            inst.assignSignature(sig, els, &a, &b);
            inst.push(Rational(a, b));
        };
        // meta: all yield truthy according to <fn>
        base.meta['≀'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                Element top = inst.pop;
                assert(top.type == ElementType.array);
                inst.push(top);
                inst.push(fn);
                inst.runAsChild("→#⊨∀");
            };
        };
        // meta: any yield truthy according to <fn>
        base.meta['∽'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                Element top = inst.pop;
                assert(top.type == ElementType.array);
                inst.push(top);
                inst.push(fn);
                inst.runAsChild("→#⊨∃");
            };
        };
        // meta: rational creation
        // doesn't work with numbers, yet
        base.meta['⁄'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            Element top = inst.pop;
            assert(top.type == ElementType.number);
            BigInt num = top.value.num;
            return delegate void(Tir inst) {
                fn(inst);
                Element next = inst.pop;
                assert(next.type == ElementType.number);
                BigInt den = next.value.num;
                inst.push(Rational(num, den));
            };
        };
        // GetIndex
        base.ops['@'] = caseFunction("@ (GetIndex)", [
            matcher([ElementType.arrayLike, ElementType.number], delegate Element(Tir inst, signature sig, Element[] args) {
                Element[] arr;
                BigInt index;
                inst.assignSignature(sig, args, &arr, &index);
                size_t resIndex = to!size_t(index % arr.length);
                return arr[resIndex];
            })
        ]);
        // swap top two
        base.ops['↔'] = delegate void(Tir inst) {
            Element[] topTwo = inst.popN(2);
            inst.pushMulti(topTwo.retro.array);
        };
        // collect/group stack into array
        base.ops['∎'] = delegate void(Tir inst) {
            size_t size = inst.stack.length;
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyN(size), sig, els));
            inst.push(els);
        };
        // collect/group N on stack into array
        base.ops['⧫'] = delegate void(Tir inst) {
            Element top = inst.pop;
            assert(top.type == ElementType.number);
            BigInt size = top.value.num;
            assert(size >= 0);
            Element[] collect;
            signature sig;
            assert(inst.matchSignature(Element.anyN(to!uint(size)), sig, collect));
            inst.push(collect);
        };
        // meta: while loop
        base.meta['⫿'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            voidTir condition;
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.oneFunc, sig, els)) {
                inst.assignSignature(sig, els, &condition);
            }
            else if(inst.matchSignature(Element.anyOne, sig, els)) {
                Element t;
                inst.assignSignature(sig, els, &t);
                condition = delegate void(Tir inst) {
                    inst.push(t);
                };
            }

            return delegate void(Tir inst) {
                while(true) {
                    condition(inst);
                    bool running = inst.pop.truthy;
                    if(!running) break;
                    fn(inst);
                }
            };
        };
        // meta: if
        base.meta['?'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                if(inst.pop.truthy) {
                    fn(inst);
                }
            };
        };
        // meta: reduce right
        base.meta['⤚'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                Element top = inst.pop;

                Element[] a = top.toArray;

                while(a.length != 1) {
                    inst.callOp(fn, a, a);
                }
                inst.push(a.pop);
            };
        };
        // meta: reduce left
        base.meta['⤙'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                Element top = inst.pop;

                Element[] a = top.toArray.retro.array;
                /* fn = meta['⇔'](inst, source, fn); */

                while(a.length != 1) {
                    inst.callOp(fn, a, a);
                }
                inst.push(a.pop);
            };
        };
        // meta: repeat N times
        base.meta['∐'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            Element top = inst.pop;
            assert(top.type == ElementType.number);
            BigInt n = top.value.num;

            return delegate void(Tir inst) {
                n.times(delegate void() {
                    fn(inst);
                });
            };
        };
        // meta: reversed arguments
        base.meta['⇔'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                inst.beforeCall = delegate void(Tir inst, ref Element[] args, ref signature sig) {
                    sig.reverse;
                    args.reverse;
                };
                fn(inst);
            };
        };
        // all are truthy
        base.ops['∀'] = delegate void(Tir inst) {
            Element top = inst.pop;
            assert(top.type == ElementType.array);
            Element[] arr = top.value.arr;

            bool res = true;
            foreach(el; arr) {
                if(!el.truthy) {
                    res = false;
                    break;
                }
            }
            inst.push(res);
        };
        // stack: duplicate TOS
        base.ops['⤇'] = delegate void(Tir inst) {
            Element top = inst.pop;
            inst.push(top);
            inst.push(top);
        };
        // stack: pop TOS
        base.ops['⤆'] = delegate void(Tir inst) {
            inst.pop;
        };
        // meta: 2d cross product/pairwise
        base.meta['⨯'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return binary("⨯ (CrossProduct)", delegate Element(Tir inst, signature sig, Element av, Element bv) {
                Element[] as, bs;
                as = av.castTo(ElementType.array).toArray;
                bs = bv.castTo(ElementType.array).toArray;
                Element[] res;
                Element[] row;
                foreach(a; as) {
                    row = [];
                    foreach(b; bs) {
                        row ~= inst.callOp(fn, a, b);
                    }
                    res ~= Element(row);
                }
                return Element(res);
            });
        };
        // unary cross product
        base.meta['⋆'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return unary(delegate Element(Tir inst, Element av) {
                Element[] as;
                as = av.castTo(ElementType.array).toArray;
                Element[] res;
                Element[] row;
                foreach(x; as) {
                    row = [];
                    foreach(y; as) {
                        row ~= inst.callOp(fn, x, y);
                    }
                    res ~= Element(row);
                }
                return Element(res);
            });
        };
        // any are truthy
        base.ops['∃'] = delegate void(Tir inst) {
            Element top = inst.pop;
            assert(top.type == ElementType.array);
            Element[] arr = top.value.arr;

            bool res = false;
            foreach(el; arr) {
                if(el.truthy) {
                    res = true;
                    break;
                }
            }
            inst.push(res);
        };
        // split-join
        base.meta['⟗'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                inst.runAsChild("⟠");
                inst.push(fn);
                inst.runAsChild("→⨝");
            };
        };
        // meta: quote function
        base.meta['$'] = delegate voidTir(Tir inst, string source, voidTir mod) {
            return delegate void(Tir inst) {
                inst.push(new Element(mod, source));
            };
        };
        // meta: thread
        base.meta['#'] = delegate voidTir(Tir inst, string source, voidTir mod) {
            return delegate void(Tir inst) {
                Element top = inst.pop.castTo(ElementType.array);
                Element[] data = top.value.arr;
                Element[] tempStack;
                inst.push(data.map!(delegate Element(Element el) {
                    inst.callOp(mod, tempStack, el);
                    Element res = tempStack.pop;
                    return res;
                }).array);
            };
        };
        // meta: zipwith
        base.meta['⨼'] = delegate voidTir(Tir inst, string source, voidTir mod) {
            return caseFunction("⨼" ~ source ~ " (ZipWithMeta)", [
                matcher(Element.twoArrays, delegate Element(Tir inst, signature sig, Element[] args) {
                    Element[] as, bs;
                    inst.assignSignature(sig, args, &as, &bs);
                    Element[] res;
                    foreach(a, b; lockstep(as, bs)) {
                        res ~= inst.callOp(mod, a, b);
                    }
                    return Element(res);
                })
            ]);
        };
        // map
        // arr func →
        base.ops['→'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature([ElementType.array, ElementType.func], sig, els));

            Element[] arr;
            voidTir fn;
            inst.assignSignature(sig, els, &arr, &fn);

            Element[] tempStack;
            inst.push(arr.map!(delegate Element(Element el) {
                inst.callOp(fn, tempStack, el);
                Element res = tempStack.pop;
                return res;
            }).array);
        };
        /* base.meta['⇷'] = delegate void(Tir inst) {
            writeln("metaa");
        }; */
        // string collection
        base.ops['s'] = delegate void(Tir inst) {
            Element top = inst.pop;
            if(top.type == ElementType.number) {
                BigInt count = top.value.num;
                Element[] members;
                signature sig = inst.popN(to!size_t(count), members);
                if(sig.all!"a == ElementType.number") {
                    inst.push(members.map!(e => to!dchar(e.value.num).text).array.join(""));
                }
            }
            else if(top.type == ElementType.string) {
                inst.push(top);
            }
            else if(top.type == ElementType.array) {
                Element[] arr = top.value.arr;
                inst.push(arr.map!(e => e.toString()).array.join(", "));
            }
        };
        base.ops['⧉'] = caseFunction("⧉ (IsPrime)", [
            matcher(Element.oneNumber, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a;
                inst.assignSignature(sig, args, &a);
                return Element(a.isPrime);
            }),
        ]);
        base.ops['+'] = caseFunction("+ (Add)", [
            matcher(Element.oneArray, delegate Element(Tir inst, signature sig, Element[] args) {
                inst.runAsChild("⤚+", args);
                return null;
            }),
            matcher(Element.twoNumbers, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a, b;
                inst.assignSignature(sig, args, &a, &b);
                return Element(a + b);
            }),
            matcher(Element.twoStrings, delegate Element(Tir inst, signature sig, Element[] args) {
                string s, t;
                inst.assignSignature(sig, args, &s, &t);
                return Element(s ~ t);
            })
        ]);
        // debug stack
        base.ops['⧌'] = delegate void(Tir inst) {
            inst.debugStack;
        };
        // subtract
        base.ops['−'] = base.ops['-'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.twoNumbers, sig, els));
            BigInt a, b;
            inst.assignSignature(sig, els, &a, &b);
            inst.push(a - b);
        };
        // modulus
        base.ops['%'] = caseFunction("% (Mod)", [
            matcher(Element.twoNumbers, delegate Element(Tir inst, signature sig, Element[] args) {
                BigInt a, b;
                inst.assignSignature(sig, args, &a, &b);
                return Element(a % b);
            }),
        ]);
        // meta: try-error
        base.meta['⧊'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            voidTir otherwise;
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.oneFunc, sig, els)) {
                otherwise = els[0].value.fun;
            }
            return delegate void(Tir inst) {
                try {
                    fn(inst);
                } catch(Exception e) {
                    if(otherwise) otherwise(inst);
                }
            };
        };
        // meta: vectorize
        base.meta['⨳'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return caseFunction("MetaVectorize (" ~ source ~ ")", [
                matcher(Element.twoArrays, delegate Element(Tir inst, signature sig, Element[] args) {
                    // resize to match
                    Element[] as, bs;
                    inst.assignSignature(sig, args, &as, &bs);
                    return Element(inst.vectorize(fn, as, bs));
                }),
                matcher([ElementType.array, ElementType.any], delegate Element(Tir inst, signature sig, Element[] args) {
                    Element[] as;
                    Element b;
                    inst.assignSignature(sig, args, &as, &b);
                    return Element(inst.vectorize(fn, as, [b]));
                }),
                matcher([ElementType.any, ElementType.array], delegate Element(Tir inst, signature sig, Element[] args) {
                    Element a;
                    Element[] bs;
                    inst.assignSignature(sig, args, &a, &bs);
                    return Element(inst.vectorize(fn, [a], bs));
                }),
            ]);
        };

        // ALIASES
        // 1-range
        base.aliasFunc('∟', "1↔1+r");
        // decrement
        base.aliasFunc('⤈', "1-");
        // increment
        base.aliasFunc('⤉', "1+");
        base.aliasFunc('⧖', "2%");
        // mod 2 sum
        base.aliasFunc('⨊', "⦾#⧖+");
        base.aliasFunc('⧗', "2%1=");
        // all ords
        base.aliasFunc('⦾', "{}⧊#o");
        base.aliasFunc('∄', "∃¬");
        base.aliasFunc('⅋', "⇔&");
    }
}

Element parseInput(string e) {
    if(e[0] == '[') {
        // parse array
        Element[] res;
        foreach(sxn; e[1..$-1].split(',')) {
            res ~= parseInput(sxn.strip);
        }
        return Element(res);
    }
    else if(e[0].isDigit) {
        return Element(BigInt(e));
    }
    else if(e[0] == '"') {
        return Element(e[1..$-1]);
    }
    else {
        return Element(e);
    }
}

class ArgumentConsumer : Consumer!Element {
    this(string[] args) {
        super(args.map!(delegate Element(string e) {
            return e.parseInput;
        }).array, Element(0));
    }
}

enum Option {
    READ_UTF,
    ENCODE
}

int main(string[] args) {
    if(args.length < 2) {
        stderr.writeln("insufficient args given");
        return -1;
    }
    size_t start = 1;
    bool[Option] config;
    config[Option.READ_UTF] = false;
    config[Option.ENCODE] = false;

    while(start < args.length && args[start][0] == '-') {
        switch(args[start][1]) {
            case 'u':
                config[Option.READ_UTF] = true;
                break;
            case 'e':
                config[Option.ENCODE] = true;
                break;

            default:
                assert(0, "unhandled flag " ~ args[start]);
        }
        start++;
    }
    string code = args[start];

    try {
        code = code.readBytes;
    }
    catch(FileException e) {
        stderr.writeln("Assuming command line argument.");
    }

    if(config[Option.ENCODE]) {
        code.encodeTir.write;
        return 0;
    }

    if(config[Option.READ_UTF]) {
        // idk
    }
    else {
        code = code.decodeTir;
    }

    start++;

    auto inst = new Tir(code);
    inst.arguments = new ArgumentConsumer(args[start..$]);

    try {
        inst.run();
    } catch(ExitException e) {
        return e.returnCode;
    } catch(TirError e) {
        stderr.writeln(e.message);
    }

    foreach(el; inst.stack) {
        writeln(el);
    }
    return 0;
    /* writeln(inst.meta.keys);
    writeln(inst.ops.keys); */
}

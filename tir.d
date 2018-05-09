import std.ascii;
import std.algorithm.iteration;
import std.algorithm.mutation;
import std.algorithm.searching;
import std.array;
import std.bigint;
import std.conv;
import std.file;
import std.functional;
import std.range;
import std.stdio;
import std.string;
import std.utf;
import core.vararg;

T pop(T)(ref T[] arr) {
    T last = arr[$ - 1];
    arr.length--;
    return last;
}
void push(T)(ref T[] arr, T el) {
    arr ~= el;
}

enum TokenType {
    number, string, command, meta, func_start, func_end, set_var, set_func, whitespace, none
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
        if(cur.isDigit) {
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
            next.raw ~= cur;
            if(cur != '{') {
                advance;
            }
            // next.raw ~= cur;
            // advance;
        }
        // quote string « ... »
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
    number, string, array, func, any
}
union ElementValue {
    BigInt num;
    string str;
    Element[] arr;
    voidTir fun;
}
class Element {
    ElementValue value;
    ElementType type;
    string repr;

    this(voidTir fun, string repr) {
        update(fun, repr);
    }
    this(int n) {
        this(BigInt(n));
    }
    this(T)(T el) {
        update(el);
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
    void update(voidTir fun) {
        update(fun, "<no representation>");
    }
    void update(voidTir fun, string repr) {
        type = ElementType.func;
        value.fun = fun;
        this.repr = repr;
    }

    bool truthy() {
        switch(type) {
            case ElementType.array:
                return true;
            case ElementType.string:
                return value.str.length != 0;
            case ElementType.number:
                return value.num != 0;
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
            case ElementType.func:
                return repr;

            default:
                assert(0);
        }
    }

    static signature oneFunc = [ElementType.func];
    static signature oneArray = [ElementType.array];
    static signature oneNumber = [ElementType.number];
    static signature anyOne = [ElementType.any];

    static signature twoNumbers = [ElementType.number, ElementType.number];
    static signature twoStrings = [ElementType.string, ElementType.string];
    static signature anyTwo = [ElementType.any, ElementType.any];
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
            if(a != b) {
                return false;
            }
        }
    }

    return true;
}

class Tir {
    Element[] stack = [];
    Token[] tokens;
    size_t ip = 0;
    voidTir[dchar] ops;
    metaTir[dchar] meta;
    Element[dchar] vars;

    // actions
    signatureAction beforeCall = null;

    Element pop() {
        if(stack.length) {
            return stack.pop;
        }
        else {
            return new Element(BigInt("0"));
        }
    }
    void push(Element el) {
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
    void push2(T, S)(T a, S b) {
        push(a);
        push(b);
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
        for(size_t i = n - 1; i < n; --i) {
            els[i] = pop;
        }
        return signatureof(els);
    }

    signature peekN(size_t n, out Element[] els) {
        els = [];
        els.length = n;
        for(size_t i = n - 1; i < n; --i) {
            /* writefln("n,i: %s,%s", n, i); */
            els[i] = stack[$ - n + i];
        }
        return signatureof(els);
    }

    bool matchSignature(signature search, out signature result, out Element[] els) {
        size_t n = search.length;
        Element[] e;
        signature sig = peekN(n, e);
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
                *a = els[i].value.arr;
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
    
    this(string code) {
        assignOps;
        tokens = code.tokenize(meta.keys);
    }
    
    this(Token[] code) {
        tokens = code;
    }
    
    this(Token[] code, Tir inst) {
        this(code);
        inherit(inst);
    }
    
    void inherit(Tir inst) {
        ops = inst.ops;
        meta = inst.meta;
        stack = inst.stack;
        vars = inst.vars;
    }
    
    void assignOps() {
        
        /* ops['h'] = delegate void(Tir inst) {
            writeln("HellO!");
        }; */
        // call/negate
        ops['~'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.oneFunc, sig, els)) {
                voidTir fn;
                assignSignature(sig, els, &fn);
                fn(inst);
            }
            else if(inst.matchSignature(Element.oneNumber, sig, els)) {
                BigInt a;
                assignSignature(sig, els, &a);
                push(-a);
            }
        };
        // range
        ops['r'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                assignSignature(sig, els, &a, &b);
                Element[] res = [];
                for(BigInt i = a; i < b; i++) {
                    res ~= new Element(i);
                }
                inst.push(res);
            }
        };
        // multiplication
        ops['×'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.oneArray, sig, els)) {
                Element[] a;
                assignSignature(sig, els, &a);

                while(a.length != 1) {
                    callOp('×', a, a);
                }
                push(a.pop);
            }
            else if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                assignSignature(sig, els, &a, &b);
                inst.push(a * b);
            }
            else {
                stderr.writeln("No matching method for `+`: " ~ els.map!(e => e.toString()).array.join(", "));
            }
        };
        // divide
        ops['÷'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                assignSignature(sig, els, &a, &b);
                inst.push(a / b);
            }
        };
        // pair
        ops[','] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature(Element.anyTwo, sig, els));
            Element a, b;
            assignSignature(sig, els, &a, &b);
            push([a, b]);
        };
        // is truthy
        ops['⊨'] = delegate void(Tir inst) {
            Element top = inst.pop;
            push(top.truthy);
        };
        // collect stack into array
        ops['∎'] = delegate void(Tir inst) {
            Element[] stack = inst.stack;
            inst.stack.length = 0;
            inst.push(stack);
        };
        // meta: reduce right
        meta['⤙'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                Element top = inst.pop;

                assert(top.type == ElementType.array);
                Element[] a = top.value.arr;

                while(a.length != 1) {
                    inst.callOp(fn, a, a);
                }
                inst.push(a.pop);
            };
        };
        // meta: repeat N times
        meta['∐'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            Element top = inst.pop;
            assert(top.type == ElementType.number);
            BigInt n = top.value.num;

            return delegate void(Tir inst) {
                foreach(e; n.iota) {
                    fn(inst);
                }
            };
        };
        // meta: reversed arguments
        meta['⇔'] = delegate voidTir(Tir inst, string source, voidTir fn) {
            return delegate void(Tir inst) {
                inst.beforeCall = delegate void(Tir inst, ref Element[] args, ref signature sig) {
                    sig.reverse;
                    args.reverse;
                };
                fn(this);
            };
        };
        // meta: reduce left
        /* meta['⤚'] = delegate void(Tir inst, string source, voidTir fn) {
            Element top = inst.pop;

            assert(top.type == ElementType.array);
            Element[] a = top.value.arr.retro.array;

            while(a.length != 1) {
                writeln("-- ", a);
                callOp(fn, a, a);
            }
            push(a.pop);
        }; */
        // all
        ops['∀'] = delegate void(Tir inst) {
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
            push(res);
        };
        // quote function
        meta['$'] = delegate voidTir(Tir inst, string source, voidTir mod) {
            return delegate void(Tir inst) {
                push(new Element(mod, source));
            };
        };
        // thread
        meta['#'] = delegate voidTir(Tir inst, string source, voidTir mod) {
            return delegate void(Tir inst) {
                Element top = inst.pop;
                assert(top.type == ElementType.array);
                Element[] data = top.value.arr;
                Element[] tempStack;
                push(data.map!(delegate Element(Element el) {
                    callOp(mod, tempStack, el);
                    Element res = tempStack.pop;
                    return res;
                }).array);
            };
        };
        // arr func →
        ops['→'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            assert(inst.matchSignature([ElementType.array, ElementType.func], sig, els));
            Element[] arr;
            voidTir fn;
            assignSignature(sig, els, &arr, &fn);
            Element[] tempStack;
            push(arr.map!(delegate Element(Element el) {
                callOp(fn, tempStack, el);
                Element res = tempStack.pop;
                return res;
            }).array);
        };
        /* meta['⇷'] = delegate void(Tir inst) {
            writeln("metaa");
        }; */
        // to string
        ops['s'] = delegate void(Tir inst) {
            Element top = inst.pop;
            if(top.type == ElementType.number) {
                BigInt count = top.value.num;
                Element[] members;
                signature sig = popN(to!size_t(count), members);
                if(sig.all!"a == ElementType.number") {
                    push(members.map!(e => to!dchar(e.value.num).text).array.join(""));
                }
            }
            else if(top.type == ElementType.string) {
                push(top);
            }
            else if(top.type == ElementType.array) {
                Element[] arr = top.value.arr;
                push(arr.map!(e => e.toString()).array.join(", "));
            }
        };
        ops['+'] = delegate void(Tir inst) {
            Element[] els;
            signature sig;
            if(inst.matchSignature(Element.oneArray, sig, els)) {
                Element[] a;
                assignSignature(sig, els, &a);

                while(a.length != 1) {
                    callOp('+', a, a);
                }
                push(a.pop);
            }
            else if(inst.matchSignature(Element.twoNumbers, sig, els)) {
                BigInt a, b;
                assignSignature(sig, els, &a, &b);
                inst.push(a + b);
            }
            else {
                stderr.writeln("No matching method for `+`: " ~ els.map!(e => e.toString()).array.join(", "));
            }
        };
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

    void push(BigInt el) {
        stack ~= new Element(el);
    }

    void advance() {
        ip++;
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

    void step() {
        Token cur = tokens[ip];
        // writeln(vars);
        if(cur.raw.length == 1 && cur.raw[0] in vars) {
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
                /* writeln("keys ", keys); */
                /* writefln("Meta of %s under %s", target, key); */
                voidTir fn;
                if(target in ops) {
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
                       .map!(to!string)
                       .array[1..$-1]
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
}

void main(string[] args) {
    if(args.length < 2) {
        stderr.writeln("insufficient args given");
        return;
    }
    string code = args[1];

    try {
        code = code.readText;
    }
    catch(FileException e) {
        stderr.writeln("Assuming command line argument.");
    }

    /* stderr.writeln("Code : ", code); */
    auto inst = new Tir(code);
    inst.run();
    foreach(el; inst.stack) {
        writeln(el);
    }
}

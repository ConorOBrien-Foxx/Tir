import std.ascii;
import std.algorithm.iteration;
import std.algorithm.searching;
import std.array;
import std.bigint;
import std.conv;
import std.file;
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
    number, command, meta, whitespace, none
}

enum string[] tokenTypeStrings = [
    "number", "command", "meta", "whitespace", "none"
];

string toString(TokenType type) {
    return tokenTypeStrings[to!int(type)];
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

    override string toString() {
        return format("Token(%s, %s, %s)", raw, type.toString(), start);
    }
}

class Tokenizer {
    protected size_t ptr = 0;
    protected dchar[] code;
    protected Token[] tokens = [];
    protected dchar[] metas;

    this(string code) {
        this(code, []);
    }

    this(string code, dchar[] metas) {
        this.code = code.byDchar.array;
        this.metas = metas;
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

    static bool isMeta(dchar c) {
        return false;
    }

    bool hasLeft() {
        return ptr < code.length;
    }

    void readRun(ref string str, bool function(dchar) validate) {
        while(hasLeft && validate(cur)) {
            str ~= cur;
            advance;
        }
    }

    string readRun(bool function(dchar) validate) {
        string res = "";
        readRun(res, validate);
        return res;
    }

    void step() {
        Token next = new Token();
        next.start = ptr;
        if(cur.isDigit) {
            next.type = TokenType.number;
            readRun(next.raw, &isDigit);
        } else if(cur.isWhite) {
            next.type = TokenType.whitespace;
            readRun(next.raw, &isWhite);
        }
        else if(metas.map!(e => e == cur).any) {
            next.type = TokenType.meta;
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
    return inst.run();
}

Token[] tokenize(string str, dchar[] metas) {
    Tokenizer inst = new Tokenizer(str, metas);
    return inst.run();
}

enum ElementType {
    number, string, array, func
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

    static signature twoNumbers = [ElementType.number, ElementType.number];
    static signature twoStrings = [ElementType.string, ElementType.string];
}

alias voidTir = void delegate(Tir);
alias metaTir = void delegate(Tir, string, voidTir);
alias signature = ElementType[];
alias signatureAction = void delegate(Tir, ref signature);

class Tir {
    Element[] stack = [];
    Token[] tokens;
    size_t ip = 0;
    voidTir[dchar] ops;
    metaTir[dchar] meta;

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
        b = pop();
        a = pop();
        return signatureof([a, b]);
    }

    signature popN(size_t n, out Element[] els) {
        els = [];
        els.length = n;
        for(size_t i = n - 1; i < n; --i) {
            els[i] = pop();
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
        if(sig == search) {
            popN(n, els);
            result = sig;
            return true;
        }
        return false;
    }

    void assignSignature(signature sig, Element[] els, ...) {
        for(size_t i = 0; i < els.length; i++) {
            auto type = _arguments[i];
            if(type == typeid(BigInt*)) {
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
                stderr.writeln("Unhandled type " ~ to!string(type));
            }
        }
    }

    this(string code) {
        ops['h'] = delegate void(Tir inst) {
            writeln("HellO!");
        };
        // call
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
            writeln("MULTIPLY!!");
        };
        // is truthy
        ops['⊨'] = delegate void(Tir inst) {
            Element top = inst.pop;
            push(top.truthy);
        };
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
        meta['$'] = delegate void(Tir inst, string source, voidTir mod) {
            push(new Element(mod, source));
        };
        // thread
        meta['#'] = delegate void(Tir inst, string source, voidTir mod) {
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

                stderr.writeln("TODO: sum");
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

        tokens = code.tokenize(meta.keys);
    }

    void callOp(voidTir fn, ref Element[] outStack, Element[] args...) {
        auto oldStack = stack;
        stack = args;
        fn(this);
        outStack = stack;
        stack = oldStack;
    }

    void push(BigInt el) {
        stack ~= new Element(el);
    }

    void advance() {
        ip++;
    }

    void step() {
        Token cur = tokens[ip];
        switch(cur.type) {
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
                dchar key = chars[0];
                dchar target = chars[1];

                /* writefln("Meta of %s under %s", target, key); */
                if(target in ops) {
                    auto fn = ops[target];
                    meta[key](this, cur.raw, fn);
                }
                else {
                    stderr.writefln("Undefined operator `%s` passed to meta `%s`", target, key);
                }
                break;

            default:
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

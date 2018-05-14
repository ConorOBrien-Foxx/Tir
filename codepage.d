import std.array;
import std.utf : byDchar, byChar;
import std.stdio;
import std.algorithm.searching : countUntil;
import std.conv : to;
// temporary encoding order


dchar[] tirCodepage() {
    // TODO: decide on an ordering
    static _codepage = [
    "⁄⫿∐⤚≀⤙∽⇔⅋∎\n⧫↔\r℘∀",
    "−⨝→⅄⨊⧌⟠÷∄⨐⅂⊨⅁⨞∃∕",
    " !\"#$%&'()*+,-./",
    "0123456789:;<=>?",
    "@ABCDEFGHIJKLMNO",
    "PQRSTUVWXYZ[\\]^_",
    "`abcdefghijklmno",
    "pqrstuvwxyz{|}~¬",
    "×",
    "①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯",
    "⑰⑱⑲⑳⟗⤏⤌⤍⤎⟁⨯",
    "⤆⤇⋆",
    ].join.byDchar.array;
    assert(_codepage.length < 256, "too many characters for a SBCS");
    return _codepage;
}

char[] encodeTir(string chars) {
    char[] res;
    foreach(c; chars.byDchar) {
        size_t ind = tirCodepage.countUntil(c);
        res ~= to!char(ind);
    }
    return res;
}

string decodeTir(string chars) {
    dchar[] build;
    foreach(c; chars) {
        size_t ind = to!size_t(c);
        build ~= tirCodepage[c];
    }
    return to!string(build);
}

string decodeTir(char[] chars) {
    return to!string(chars).decodeTir;
}

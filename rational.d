import std.bigint;
import std.format;
import std.stdio : writeln;
import std.conv : to;
import std.utf : byDchar;
import std.array;
import std.algorithm.iteration : map;
import std.algorithm.mutation : stripRight;
import std.math : floor;
import std.traits : isIntegral;
import std.math : abs;

// D's gcd is weird for bigints
BigInt safegcd(BigInt a, BigInt b) {
    if(b == BigInt("0")) {
        return a;
    }
    else {
        return safegcd(b, a % b);
    }
}

class Rational {
private:
    BigInt numerator;
    BigInt denominator;

public:
    this(BigInt n, BigInt d) {
        numerator = n;
        denominator = d;
        cancel;
    }

    this(real d) {
        BigInt den = 1;
        while(d - d.floor > 0) {
            den *= 10;
            d *= 10;
        }
        BigInt num = BigInt(to!string(d.floor));
        this(num, den);
    }

    this(T, K)(T n, K d) {
        this(BigInt(to!string(n)), BigInt(to!string(d)));
    }

    void cancel() {
        BigInt gcd = safegcd(numerator, denominator).abs;
        numerator /= gcd;
        denominator /= gcd;

        // denominator should always be positive
        if(denominator < 0) {
            numerator *= -1;
            denominator = denominator.abs;
        }
    }

    unittest {
        Rational zero = new Rational(0);
        assert(zero.numerator == 0);
        assert(zero.denominator == 1);

        Rational decimalHalf = new Rational(0.5);
        assert(decimalHalf.numerator == 1);
        assert(decimalHalf.denominator == 2);

        Rational oneHalf = new Rational(1, 2);
        assert(oneHalf.numerator == 1);
        assert(oneHalf.denominator == 2);

        Rational complicatedOneSeventh = new Rational(111, 777);
        assert(complicatedOneSeventh.numerator == 1);
        assert(complicatedOneSeventh.denominator == 7);

        Rational negativeHalfA = new Rational(1, -2);
        assert(negativeHalfA.numerator == -1);
        assert(negativeHalfA.denominator == 2);

        Rational negativeHalfB = new Rational(-1, 2);
        assert(negativeHalfB.numerator == -1);
        assert(negativeHalfB.denominator == 2);

        Rational negativeHalfC = new Rational(-1, -2);
        assert(negativeHalfC.numerator == 1);
        assert(negativeHalfC.denominator == 2);

    }

    static Rational opCall(T, K)(T n, K d) {
        return new Rational(n, d);
    }
    static Rational opCall(real n) {
        return new Rational(n);
    }
    static Rational opCall(T)(T n) {
        return new Rational(n, 1);
    }

    unittest {
        Rational oneHalf = Rational(1, 2);
        assert(oneHalf.numerator == 1);
        assert(oneHalf.denominator == 2);

        Rational complicatedOneSeventh = Rational(111, 777);
        assert(complicatedOneSeventh.numerator == 1);
        assert(complicatedOneSeventh.denominator == 7);

        Rational seventeen = Rational(17);
        assert(seventeen.numerator == 17);
        assert(seventeen.denominator == 1);
    }


    override bool opEquals(Object other) {
        if(typeid(other) == typeid(Rational)) {
            Rational r = cast(Rational) other;
            return numerator == r.numerator && denominator == r.denominator;
        }
        return false;
    }
    bool opEquals(T)(T other) if (isIntegral!T) {
        return denominator == 1 && numerator == other;
    }

    unittest {
        assert(Rational(1, 2) == Rational(3, 6));
        assert(Rational(100) == Rational(100, 1));
        assert(Rational(9, 3) == Rational(3));
        assert(Rational(9, 3) == 3);
        assert(Rational(111, 777) == Rational(1, 7));
    }

    Rational opAssign(T)(const T other) pure nothrow if (isIntegral!T) {
        numerator = other.numerator;
        denominator = other.denominator;
        return this;
    }

    unittest {
        auto a = Rational(1, 2);
        a = Rational(1, 3);
        assert(a == Rational(1, 3));
    }

    Rational negate() {
        return Rational(-numerator, denominator);
    }

    unittest {
        auto a = Rational(1, 2);
        assert(-a == Rational(-1, 2));
        assert(a == -Rational(-1, 2));
    }

    Rational reciprocal() {
        return Rational(denominator, numerator);
    }

    unittest {
        auto a = Rational(1, 2);
        assert(a.reciprocal == 2);
        assert(a.reciprocal.reciprocal == a);
        assert(Rational(4, 3).reciprocal == Rational(3, 4));
    }

    Rational multiply(Rational other) {
        return Rational(
            numerator * other.numerator,
            denominator * other.denominator
        );
    }
    Rational multiply(T)(T other) {
        return mixin("multiply(Rational(other))");
    }

    unittest {
        // 1/2 * 1/2 = 1/4
        assert(Rational(1, 2).multiply(Rational(1, 2)) == Rational(1, 4));
        // 1/2 * 2 = 1
        assert(Rational(1, 2).multiply(Rational(2)) == Rational(1));
        // 3/7 * 1/4 = 3/28
        assert(Rational(3, 7).multiply(Rational(1, 4)) == Rational(3, 28));
        // 3/4 * 4 == 3
        assert(Rational(3, 4).multiply(4) == 3);
        // 9/12 * 0 = 0
        assert(Rational(9, 12).multiply(0) == 0);
    }

    Rational divide(Rational other) {
        return multiply(other.reciprocal);
    }
    Rational divide(real other) {
        return mixin("multiply(Rational(other).reciprocal)");
    }
    Rational divide(T)(T other) {
        return mixin("multiply(Rational(1, other))");
    }

    unittest {
        // (1/4) / 2 == 1/8
        assert(Rational(1, 4).divide(2) == Rational(1, 8));
        // (1/4) / (1/4) == 1
        assert(Rational(1, 4).divide(Rational(1, 4)) == 1);
        // (3/2) / 3 == 1/2
        assert(Rational(3, 2).divide(3) == Rational(1, 2));
    }

    Rational add(Rational other) {
        return Rational(
            numerator * other.denominator + other.numerator * denominator,
            denominator * other.denominator
        );
    }
    Rational add(T)(T other) {
        return mixin("add(Rational(other))");
    }

    unittest {
        // 1/4 + 1/3 == 7/12
        assert(Rational(1, 4).add(Rational(1, 3)) == Rational(7, 12));
        // 1/7 + 1 = 8/7
        assert(Rational(1, 7).add(1) == Rational(8, 7));
    }

    Rational subtract(Rational other) {
        return add(other.negate);
    }
    Rational subtract(T)(T other) {
        return mixin("add(-Rational(other))");
    }

    unittest {
        // 1/2 - 1/2 == 0
        assert(Rational(1, 2).subtract(Rational(1, 2)) == 0);
        // 1/2 - 1 == -1/2
        assert(Rational(1, 2).subtract(1) == Rational(-1, 2));
    }

    Rational opUnary(string op)() {
        static if(op == "-")      return mixin("negate");
        else static if(op == "~") return mixin("reciprocal");
        else static assert(0, "Unary operator " ~ op ~ " not implemented for `Rational`s.");
    }

    unittest {
        // -(1/2) == (-1)/2
        assert(-Rational(1, 2) == Rational(-1, 2));

        // 1/(1/4) == 4
        assert(~Rational(1, 4) == 4);

        // 1/(2/3) == 3/2
        assert(~Rational(2, 3) == Rational(3, 2));
    }

    Rational opBinary(string op)(Rational rhs) {
        static if(op == "*")      return mixin("multiply(rhs)");
        else static if(op == "+") return mixin("add(rhs)");
        else static if(op == "-") return mixin("subtract(rhs)");
        else static if(op == "/") return mixin("divide(rhs)");
        else static assert(0, "Binary operator " ~ op ~ " not implemented for `Rational`s.");
    }

    unittest {
        // 1/2 * 1/2 = 1/4
        assert(Rational(1, 2) * Rational(1, 2) == Rational(1, 4));
        // 1/2 * 2 = 1
        assert(Rational(1, 2) * Rational(2) == Rational(1));
        // 3/7 * 1/4 = 3/28
        assert(Rational(3, 7) * Rational(1, 4) == Rational(3, 28));
    }

    Rational opBinary(string op, T)(T rhs) {
        return mixin("this " ~ op ~ " Rational(rhs)");
    }

    unittest {
        // 1/2 * 2 == 1
        assert(Rational(1, 2) * 2 == 1);
        // 1/2 * 0.5 = 1/4
        assert(Rational(1, 2) * 0.5 == Rational(1, 4));

        // 1/2 + 1/2 == 1
        assert(Rational(1, 2) + Rational(1, 2) == 1);
        // 1/3 + 1/2 == 5/6
        assert(Rational(1, 3) + Rational(1, 2) == Rational(5, 6));

        // 1/2 - 1/2 == 0
        assert(Rational(1, 2) - Rational(1, 2) == 0);
        // 1/3 - 1/2 == -1/6
        assert(Rational(1, 3) - Rational(1, 2) == -Rational(1, 6));

        // (1/2) / 2 == 1/4
        assert(Rational(1, 2) / 2 == Rational(1, 4));
        
        // (1/2) / 0.5 = 1
        assert(Rational(1, 2) / 0.5 == 1);
    }

    // performs integer division
    BigInt opCast(BigInt)() {
        return numerator / denominator;
    }

    unittest {
        // 5.0 / 2.0 == 2.5 (rounds down to) 2
        assert(cast(BigInt) Rational(5, 2) == 2);
        // 4.0 / 2.0 == 2.0 (rounds down to) 2
        assert(cast(BigInt) Rational(4, 2) == 2);
        // 3.0 / 2.0 == 1.5 (rounds down to) 1
        assert(cast(BigInt) Rational(3, 2) == 1);
    }

    string decimalForm(size_t place = 20) {
        auto mul = this * BigInt(10) ^^ place;
        dchar[] res = to!string(to!BigInt(mul)).byDchar.array;

        res.insertInPlace(res.length - place, '.');

        // prepend 0 if representation starts with a `.`
        // e.g. ".25" becomes "0.25"
        if(res[0] == '.') {
            res = '0' ~ res;
        }

        // remove trailing 0's and decimal points
        // e.g. "5.000000" becomes "5" and "2.25000" becomes "2.25"
        return res.stripRight('0')
                  .stripRight('.')
                  .map!(to!string)
                  .join;
    }

    unittest {
        assert(Rational(5, 2).decimalForm == "2.5");
        assert(Rational(5).decimalForm == "5");
        assert(Rational(1, 3).decimalForm == "0.33333333333333333333");
        assert(Rational(1, 3).decimalForm(2) == "0.33");
        assert(Rational(2, 3).decimalForm(2) == "0.66");
        assert(Rational(3, 3).decimalForm(2) == "1");
        assert(Rational(104348, 33215).decimalForm(6) == "3.141592");
    }

    override string toString() {
        return format("%s/%s", numerator, denominator);
    }
}

void main() {
    /* writeln(Rational(1, 2) - Rational(1, 2)); */
    /* writeln(Rational(104348, 33215).decimalForm(6)); */
    /* auto test = Rational(104348, 33215);
    writeln(test == test);
    writeln(test.toFixed(100)); */
}

#include <iostream>
#include <cmath>
#include <vector>
#include <bitset>
#include <algorithm>
#include <string>
#include <complex>
#include <functional>
#include <cassert>
#include <valarray>
#include <numeric>
#include <execution>

using namespace std;

const uint64_t BASE_POWER = 9;

typedef long double ldouble;
typedef complex<ldouble> Complex;

const ldouble PI = acosl(-1);


uint64_t next_pow2(uint64_t value, unsigned maxb = sizeof(uint64_t) * CHAR_BIT, unsigned curb = 1) {
	return maxb <= curb ? value : next_pow2(((value - 1) | ((value - 1) >> curb)) + 1, maxb, curb << 1);
}

uint64_t lg(uint64_t n) {
	return n == 1 ? 0 : 1 + lg(n >> 1);
}

uint64_t sqr(uint64_t a) {
	return a * a;
}

uint64_t power(uint64_t a, uint64_t n) {
	return n == 0 ? 1 : sqr(power(a, n / 2)) * (n % 2 == 0 ? 1 : a);
}

valarray<Complex> pow(valarray<Complex> a, int64_t power_) {
	transform(begin(a), end(a), begin(a), [power_](Complex base) { return pow(base, power_); });
	return a;
}

class LNum {
	vector<uint64_t> parts;
	const uint64_t base = std::pow(10, BASE_POWER);
	uint64_t N, P;
public:
	LNum(string str) {
		while (str.length() >= BASE_POWER) {
			parts.push_back(stoull(str.substr(str.length() - BASE_POWER, BASE_POWER)));
			str.erase(str.length() - BASE_POWER, BASE_POWER);
		}
		if (str.length() > 0) {
			parts.push_back(stoull(str.substr(0, str.length())));
		}
	}

	LNum(uint64_t i) : LNum(to_string(i)) {}

	uint64_t bits() {
		LNum var = *this;
		uint64_t bits;
		for (bits = 0; var != 0; ++bits) var /= 2;
		return bits;
	}

	LNum& operator +=(const LNum& rhs) {
		*this = *this + rhs;
		return *this;
	}

	LNum operator+(const LNum& rhs) const {
		LNum lhs = *this;
		uint64_t carry = 0;
		for (size_t i = 0; i < max(lhs.parts.size(), rhs.parts.size()) || carry; ++i) {
			if (i == lhs.parts.size())
				lhs.parts.push_back(0);
			lhs.parts[i] += carry + (i < rhs.parts.size() ? rhs.parts[i] : 0);
			carry = lhs.parts[i] >= base;
			if (carry) lhs.parts[i] -= base;
		}
		return lhs;
	}

	static LNum plus_mod(const LNum& rhs, const LNum& lhs, uint64_t mod) {
		return ((rhs % mod) + (lhs % mod)) % mod;
	}
	static LNum minus_mod(const LNum& rhs, const LNum& lhs, uint64_t mod) {
		return ((rhs % mod) - (lhs % mod)) % mod;
	}
	static LNum mul_mod(const LNum& rhs, const LNum& lhs, uint64_t mod) {
		return ((rhs % mod) * (lhs % mod)) % mod;
	}
	static LNum div_mod(const LNum& rhs, const LNum& lhs, uint64_t mod) {
		return ((rhs % mod) / (lhs % mod)) % mod;
	}
	static LNum mod_mod(const LNum& rhs, const LNum& lhs, uint64_t mod) {
		return ((rhs % mod) % (lhs % mod)) % mod;
	}
	LNum pow_mod(LNum exp, LNum modulus) {
		LNum base = *this;
		base = base % modulus;
		LNum result = 1;
		while (exp > 0) {
			if ((exp % 2) == 1) 
				result = (result * base) % modulus;
			base = (base * base) % modulus;
			exp = exp / 2;
		}
		return result;
	}

	LNum& operator -=(const LNum& rhs) {
		*this = *this - rhs;
	}

	LNum operator-(const LNum& rhs) const {
		LNum lhs = *this;
		uint64_t carry = 0;
		for (size_t i = 0; i < rhs.parts.size() || carry; ++i) {
			lhs.parts[i] -= carry + (i < rhs.parts.size() ? rhs.parts[i] : 0);
			carry = lhs.parts[i] < 0;
			if (carry) lhs.parts[i] += base;
		}
		while (lhs.parts.size() > 1 && lhs.parts.back() == 0)
			lhs.parts.pop_back();

		return lhs;
	}

	LNum& operator /=(const LNum& rhs) {
		*this = *this / rhs;
		return *this;
	}

	LNum operator /(const LNum& rhs) const {
		LNum lhs = *this;
		LNum res(0);
		res.parts.resize(lhs.parts.size());
		LNum curValue(0);
		for (int64_t i = lhs.parts.size() - 1; i >= 0; i--)
		{
			curValue *= base;

			curValue.parts[0] = lhs.parts[i];
			// подбираем максимальное число x, такое что b * x <= curValue
			uint64_t x = 0;
			uint64_t l = 0, r = base;
			while (l <= r)
			{
				uint64_t m = (l + r) >> 1;
				LNum cur = rhs * m;
				if (cur <= curValue)
				{
					x = m;
					l = m + 1;
				}
				else {
					r = m - 1;
				}
			}
			res.parts[i] = x;
			curValue = curValue - rhs * LNum(x);
		}

		while (res.parts.size() > 1 && res.parts.back() == 0)
			res.parts.pop_back();
		return res;
	}

	LNum& operator %=(const LNum& rhs) {
		*this = *this % rhs;
	}

	LNum operator %(const LNum& rhs) const {
		LNum lhs = *this;
		LNum res(0);
		res.parts.resize(lhs.parts.size());
		LNum curValue(0);
		for (int64_t i = lhs.parts.size() - 1; i >= 0; i--)
		{
			curValue *= (base);

			curValue.parts[0] = lhs.parts[i];
			// подбираем максимальное число x, такое что b * x <= curValue
			uint64_t x = 0;
			uint64_t l = 0, r = base;
			while (l <= r)
			{
				uint64_t m = (l + r) >> 1;
				LNum cur = rhs * m;
				if (cur <= curValue)
				{
					x = m;
					l = m + 1;
				}
				else {
					r = m - 1;
				}
			}
			res.parts[i] = x;
			curValue = curValue - rhs * LNum(x);
		}
		while (curValue.parts.size() > 1 && curValue.parts.back() == 0)
			curValue.parts.pop_back();
		return curValue;
	}

	LNum& operator %=(const uint64_t& rhs) {
		*this = *this % rhs;
	}

	int64_t operator %(const uint64_t& rhs) const {
		LNum lhs = *this;
		int64_t carry = 0;
		for (int64_t i = (int64_t)lhs.parts.size() - 1; i >= 0; --i) {
			int64_t cur = lhs.parts[i] + carry * 1ll * base;
			lhs.parts[i] = int64_t(cur / rhs);
			carry = int64_t(cur % rhs);
		}
		return carry;
	}

	LNum& operator *=(const LNum& rhs) {
		*this = *this * rhs;
		return *this;
	}

	LNum operator *(const LNum& rhs) const {
		LNum lhs = *this;
		vector<uint64_t> c((lhs.parts.size() + rhs.parts.size()) * 2);
		for (size_t i = 0; i < lhs.parts.size(); ++i)
			for (size_t j = 0, carry = 0; j < rhs.parts.size() || carry; ++j) {
				uint64_t cur = c[i + j] + lhs.parts[i] * 1ll * (j < (uint64_t)rhs.parts.size() ? rhs.parts[j] : 0) + carry;
				c[i + j] = uint64_t(cur % base);
				carry = uint64_t(cur / base);
			}
		while (c.size() > 1 && c.back() == 0)
			c.pop_back();
		lhs.parts = c;
		return lhs;
	}

	LNum& operator *=(const uint64_t& rhs) {
		*this = *this * rhs;
		return *this;
	}

	LNum operator *(const uint64_t& rhs) const {
		LNum lhs = *this;
		uint64_t carry = 0;
		for (size_t i = 0; i < lhs.parts.size() || carry; ++i) {
			if (i == lhs.parts.size())
				lhs.parts.push_back(0);
			uint64_t cur = carry + lhs.parts[i] * 1ll * rhs;
			lhs.parts[i] = uint64_t(cur % base);
			carry = uint64_t(cur / base);
		}
		while (lhs.parts.size() > 1 && lhs.parts.back() == 0)
			lhs.parts.pop_back();
		return lhs;
	}

	LNum& operator ^=(const LNum& rhs) {
		*this = *this ^ rhs;
		return *this;
	}

	LNum operator ^(const LNum& rhs) const {
		LNum res(1);
		LNum cur = *this;
		LNum temp = rhs;
		while (LNum(0) != temp) {
			if (temp % 2 == 1)
				res *= cur;
			cur *= cur;
			temp /= 2;
		}
		return res;
	}

	valarray<Complex> ComputeZeta() {
		valarray<Complex> zeta(P);
		for (uint64_t k = 0; k < P; ++k) {
			zeta[k] = exp(1il * PI * ldouble(2 * k + 1) / ldouble(N));
		}
		return zeta;
	}

	LNum& mulFur(LNum rhs) {
		const uint64_t n = next_pow2(this->bits() + rhs.bits());
		P = next_pow2(log2(n));
		N = 2 * n / std::pow(P, 2);

		auto x = exp(1il * PI / ldouble(P)) * exp(1il * PI / ldouble(P));

		valarray<Complex> dzeta = ComputeZeta();

		auto a = half_fft(decompose(*this), dzeta);
		auto a1 = compose(inv_half_fft(a, dzeta)).to_str();
		auto b = half_fft(decompose(rhs), dzeta);
		auto b1 = compose(inv_half_fft(b, dzeta)).to_str();

		vector<valarray<Complex>> c(N);
		for (size_t i = 0; i < N; ++i) {
			//c[i].resize(P);
			//valarray<ldouble> f1(P);
			//valarray<ldouble> f2(P);
			//for (uint64_t j = 0; j < P; ++j) {
			//	f1[j] = (a[i][j].real() * b[i][j].real() - a[i][j].imag() * b[i][j].imag()); //% (std::pow(2, n) + 1);
			//	f2[j] = (a[i][j].real() * b[i][j].imag() + a[i][j].imag() * b[i][j].real());// % (std::pow(2, n) + 1);
			//}
			//transform(begin(f1), end(f1), begin(f2), begin(c[i]), [](ldouble da, ldouble db) {
			//	return Complex(da, db);
			//});
			c[i] = a[i] * b[i];
		}

		*this = compose(inv_half_fft(c, dzeta));
		return *this;
	}

	static LNum mulFur(LNum lhs, LNum rhs)
	{
		return lhs.mulFur(rhs);
	}

	bool operator <(const LNum& rhs) {
		if (parts.size() != rhs.parts.size())
			return parts.size() < rhs.parts.size();
		for (int64_t i = parts.size() - 1; i >= 0; --i)
			if (parts[i] != rhs.parts[i])
				return parts[i] < rhs.parts[i];
		return false;
	}

	bool operator >(const LNum& rhs) {
		return !(*this <= rhs);
	}

	bool operator <=(const LNum& rhs) {
		return *this < rhs || *this == rhs;
	}

	bool operator >=(const LNum& rhs) {
		return !(*this < rhs);
	}

	bool operator == (const LNum& rhs) {
		if (parts.size() != rhs.parts.size())
			return false;
		for (int64_t i = parts.size() - 1; i >= 0; --i)
			if (parts[i] != rhs.parts[i])
				return false;
		return true;
	}

	bool operator != (const LNum& rhs) {
		return !(*this == rhs);
	}

	LNum& operator=(const LNum& other)
	{
		if (&other == this)
			return *this;
		parts = other.parts;
		return *this;
	}

	friend ostream& operator<<(ostream& os, const LNum& dt);

	LNum sqrt() {
		LNum l(0);
		LNum r = *this;
		LNum res(0);
		while (l <= r)
		{
			LNum m = (l + r) / 2;
			if (m * m <= *this)
			{
				res = m;
				l = m + 1;
			}
			else
				r = m - 1;
		}
		return res;
	}

	string to_str() const {
		string res;
		char buff[BASE_POWER + 1];
		snprintf(buff, sizeof(buff), "%d", parts.empty() ? 0 : parts.back());
		res += buff;
		for (size_t i = parts.size() - 2; i != -1; --i) {
			snprintf(buff, sizeof(buff), "%09d", parts[i]);
			res += buff;
		}
		return res;
	}

private:
	vector<vector<uint64_t>> decompose(LNum l) {
		vector<vector<uint64_t>> a(N);
		for (uint64_t i = 0; i < N; ++i) {
			a[i].resize(P);
			for (uint64_t j = 0; j < P / 2; ++j) {
				a[i][j] = l % std::pow(2, P);
				l /= std::pow(2, P);
			}
			for (uint64_t j = P / 2; j < P; ++j) {
				a[i][j] = 0;
			}
		}
		return a;
	}

	LNum compose(vector<valarray<Complex>> a0) {
		LNum v(0);
		//for (int64_t i = 0; i < N; ++i) {
		//	for (int64_t j = 0; j < P; ++j) {
		//		v.plus(LNum(a0[i][j].real()).mul(LNum(2).pow(i * (P * P / 2) + j * P)));
		//	}
		//}
		vector<valarray<uint64_t>> a(N);
		for (uint64_t i = 0; i < N; ++i) {
			a[i].resize(P);
			transform(begin(a0[i]), end(a0[i]), begin(a[i]), [](const Complex& c) { return round(c.real()); });
		}

		for (int64_t j = P - 1; j >= P / 2; --j) {
			v = v * uint64_t(std::pow(2, P)) + a[N - 1][j];
		}
		for (int64_t i = N - 1; i >= 1; --i) {
			for (int64_t j = P / 2 - 1; j >= 0; --j) {
				v = v * uint64_t(std::pow(2, P)) + a[i][j] + a[i - 1][j + P / 2];
			}
		}
		for (int64_t j = P / 2 - 1; j >= 0; --j) {
			v = v * uint64_t(std::pow(2, P)) + a[0][j];
		}
		return v;//v.mod(LNum(2).pow(n));
	}

	vector<valarray<Complex>> fft(vector<valarray<Complex>> a, valarray<Complex> w_, uint64_t N_) {
		if (N_ == 1) {
			return a;
		}
		else if (N_ == 2) {
			vector<valarray<Complex>> b(N_);
			b[0] = a[0] + a[1];
			b[1] = a[0] - a[1];
			return b;
		}

		assert(N_ >= 4);
		const uint64_t J = (N_ <= 2 * P) ? 2 : 2 * P;
		const uint64_t K = N_ / J;

		vector<vector<valarray<Complex>>> c(K);
		assert(K > 0);
		for (uint64_t k = 0; k < K; ++k) {
			c[k].resize(J);
			for (uint64_t k1 = 0; k1 < J; ++k1) {
				c[k][k1] = a[k1 * K + k];
			}

			c[k] = fft(c[k], ::pow(w_, 2), J);
		}

		vector<valarray<Complex>> b(N_);
		for (uint64_t j = 0; j < J; ++j) {
			vector<valarray<Complex>> d_j(K);
			for (uint64_t k = 0; k < K; ++k) {
				d_j[k] = c[k][j] * ::pow(w_, j * k);
			}

			d_j = fft(d_j, ::pow(w_, J), K);

			for (uint64_t j1 = 0; j1 < K; ++j1) {
				b[j1 * J + j] = d_j[j1];
			}
		}

		return b;
	}

	vector<valarray<Complex>> half_fft(vector<vector<uint64_t>> a_real, valarray<Complex> dzeta) {
		vector<valarray<Complex>> a(N);
		for (size_t i = 0; i < N; ++i) {
			a[i].resize(P);
			for (size_t j = 0; j < P; ++j) {
				a[i][j] = Complex(a_real[i][j], 0);
			}
		}
		for (uint64_t k = 0; k < N; ++k) {
			a[k] *= ::pow(dzeta, k);
		}
		return fft(a, ::pow(dzeta, 2), N);
	}

	vector<valarray<Complex>> inv_half_fft(vector<valarray<Complex>> c, valarray<Complex> dzeta) {
		valarray<Complex> w = ::pow(dzeta, 2);

		vector<valarray<Complex>> b = fft(c, ::pow(w, -1), N);

		for (int64_t k = 0; k < N; ++k) {
			b[k] = b[k] * ::pow(dzeta, ldouble(-k)) / N;
		}

		return b;
	}
};

ostream& operator<<(ostream& os, const LNum& ln) {
	string x = ln.to_str();
	os << ln.to_str();
	return os;
}

LNum mulInv(LNum a, LNum mod) {
	LNum b = a % mod;
	for (LNum x = 1; x < mod; x+=1) {
		if ((b * x) % mod == 1) {
			return x;
		}
	}
	throw invalid_argument("n_i are not pairwise co-prime!");
}

LNum chineseRemainder(vector<LNum> n, vector<LNum> a) {
	LNum prod = reduce(std::execution::seq, n.begin(), n.end(), LNum(1), [](LNum a, LNum b) { return a * b; });

	LNum sm = 0;
	for (size_t i = 0; i < n.size(); ++i) {
		LNum p = prod / n[i];
		sm += a[i] * mulInv(p, n[i]) * p;
	}

	return sm % prod;
}

int main() {
	LNum("512146555550729317089") % LNum("98723459723");
	cout << LNum("24523748428").pow_mod(LNum("6500000"), LNum("98723459723")) << '\n';  //88398031434 3007310280
	cout << "123456789876543212345678987654321 * 159753579515975357951: " << LNum("123456789876543212345678987654321") * LNum("159753579515975357951") << '\n';
	cout << "sqrt(9^40): " << LNum("147808829414345923316083210206383297601").sqrt().to_str() << '\n';
	cout << "9^20: " << (LNum("9")^20).to_str() << '\n';
	cout << "10^20+1 > 10^20: " << (((LNum("10")^20) < LNum("10")^20 + 1) ? "true" : "false") << '\n';
	cout << "1234567^1234: " << (LNum("1234567") ^ LNum("1234")) << '\n';



	cout << "x = 16 (mod 17)\nx = 22 (mod 23)\nx = 30 (mod 31)\n";
	vector<LNum> n = { 17, 23, 31 };
	vector<LNum> a = { 16, 22, 30 };
	try {
		cout << chineseRemainder(n, a).to_str() << '\n' << endl;
	}
	catch (invalid_argument error) {
		cout << error.what() << "\n\n";
	}

}

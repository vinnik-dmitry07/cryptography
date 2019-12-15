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
#include <map>
#include <tuple>
#include <random>

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
#if _DEBUG
	string repr;
#endif
public:
	LNum(string str) {
		while (str.length() >= BASE_POWER) {
			parts.push_back(stoull(str.substr(str.length() - BASE_POWER, BASE_POWER)));
			str.erase(str.length() - BASE_POWER, BASE_POWER);
		}
		if (str.length() > 0) {
			parts.push_back(stoull(str.substr(0, str.length())));
		}
#if _DEBUG
		repr = to_str();
#endif
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
			if ((exp % 2) == 1) {
				result = (result * base) % modulus;
			}

			base = (base * base) % modulus;
			exp = exp / 2;
		}
		return result;
	}

	LNum& operator -=(const LNum& rhs) {
		if (*this < rhs) throw;
		*this = *this - rhs;
		return *this;
	}

	LNum operator-(const LNum& rhs) const {
		if (rhs.repr == "3418")
			true == true;

		LNum lhs = *this;
		uint64_t carry = 0;
		for (size_t i = 0; i < rhs.parts.size() || carry; ++i) {
			uint64_t temp = carry + (i < rhs.parts.size() ? rhs.parts[i] : 0);
			carry = lhs.parts[i] < temp;
			if (carry) {
				if (base < temp) throw;
				lhs.parts[i] += base - temp;
			}
			else {
				lhs.parts[i] -= temp;
			}

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
		LNum res = 0;
		res.parts.resize(lhs.parts.size());
		LNum curValue = 0;
		for (int64_t i = lhs.parts.size() - 1; i >= 0; i--) {
			curValue = curValue * base;

			curValue.parts[0] = lhs.parts[i];
			// подбираем максимальное число x, такое что b * x <= curValue
			int64_t x = 0;
			int64_t l = 0, r = base;
			while (l <= r) {
				int64_t m = (l + r) >> 1;
				LNum cur = rhs * m;
				if (cur <= curValue) {
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
		return *this;
	}

	LNum operator %(const LNum& rhs) const {
		LNum lhs = *this;
		LNum res = 0;
		res.parts.resize(lhs.parts.size());
		LNum curValue = 0;
		for (ptrdiff_t i = lhs.parts.size() - 1; i >= 0; i--) {
			curValue = curValue * base;

			curValue.parts[0] = lhs.parts[i];
			// подбираем максимальное число x, такое что b * x <= curValue
			int64_t x = 0;
			int64_t l = 0, r = base;
			while (l <= r) {
				int64_t m = (l + r) >> 1;
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
			curValue -= rhs * LNum(x);
		}

		return curValue;
	}

	LNum& operator %=(const uint64_t& rhs) {
		*this = *this % rhs;
		return *this;
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
		LNum res = 1;
		LNum cur = *this;
		LNum temp = rhs;
		while (temp != 0) {
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

	LNum& operator=(const LNum& other) {
		if (&other == this)
			return *this;
		parts = other.parts;
#if _DEBUG
		repr = to_str();
#endif
		return *this;
	}

	friend ostream& operator<<(ostream& os, const LNum& dt);
	
	static LNum abs_sub(LNum lhs, LNum rhs) {
		return lhs > rhs ? lhs - rhs : lhs - rhs;
	}

	LNum sqrt() {
		LNum l = 0;
		LNum r = *this;
		LNum res = 0;
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
		snprintf(buff, sizeof(buff), "%llu", parts.empty() ? 0 : parts.back());
		res += buff;
		for (ptrdiff_t i = parts.size() - 2; i >= 0; --i) {
			snprintf(buff, sizeof(buff), "%09llu", parts[i]);
			res += buff;
		}
		return res;
	}

	uint64_t to_int() const {
		if (LNum(numeric_limits<uint64_t>::max()) >= *this) {
			return stoull(this->to_str());
		}
		else {
			throw;
		}
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
		LNum v = 0;
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
	for (LNum x = 1; x < mod; x += 1) {
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

vector<LNum> factorization(LNum n) {
	vector<LNum> res;
	LNum i(2);

	while (n != 1) {
		while (n % i == 0) {
			res.push_back(i);
			n /= i;
		}
		i += 1;
	}
	return res;
}

int powmod(int a, int b, int m) {
	int res = 1;
	while (b > 0) {
		if (b & 1) {
			res = (res * 1ll * a) % m;
		}
		a = (a * 1ll * a) % m;
		b >>= 1;
	}
	return res;
}

int solve(int a, int b, int m) {
	int n = (int)sqrt(m + .0) + 1;
	map<int, int> vals;
	for (int p = n; p >= 1; --p)
		vals[powmod(a, p * n, m)] = p;
	for (int q = 0; q <= n; ++q) {
		int cur = (powmod(a, q, m) * 1ll * b) % m;
		if (vals.count(cur)) {
			int ans = vals[cur] * n - q;
			return ans;
		}
	}
	return -1;
}

LNum dl(LNum a, LNum b, LNum m) {
	LNum n = m.sqrt() + 1;
	map<LNum, LNum> vals;
	//
	//for (LNum p = n; p >= LNum(1); p -= 1)
	//	vals[a.pow_mod(p * n, m)] = p;
	return 0;
	/*for (LNum q = 0; q <= n; q += 1) {
		LNum cur = (a.pow_mod(q, m) * b) % m;
		if (vals.count(cur)) {
			LNum ans = vals[cur] * n - q;
			return ans;
		}
	}
	throw;*/
}

LNum totient(LNum n) {
	LNum tot = n;
	LNum i = 0;

	for (i = 2; i * i <= n; i += 2) {
		if (n % i == 0) {
			while (n % i == 0)
				n /= i;
			tot -= tot / i;
		}

		if (i == 2)
			i = 1;
	}

	if (n > 1)
		tot -= tot / n;

	return tot;
}

int16_t mobius(LNum n) {
	int8_t p = 0;

	if (n % 2 == 0) {
		n = n / 2;
		p++;

		if (n % 2 == 0)
			return 0;
	}

	const LNum ii = n.sqrt();
	for (LNum i = 3; i <= ii; i = i + 2) {
		if (n % i == 0) {
			n = n / i;
			p++;

			if (n % i == 0)
				return 0;
		}
	}

	return (p % 2) ? 1 : -1;
}

// https://en.wikipedia.org/wiki/Jacobi_symbol
int16_t jacobi(LNum a, LNum n) {
	assert(n > a&& a > 0 && n % 2 == 1);
	a %= n;
	int8_t res = 1;
	while (a != 0) {
		while (a % 2 == 0) {
			a /= 2;
			LNum r = n % 8;
			if (r == 3 || r == 5) res = -res; // 9: (2a | n) = -(a | n) if n = 3, 5 (mod 8) else (a | n)
		}
		swap(a, n);
		if (a % 4 == 3 && n % 4 == 3)
			res = -res; // 6: (a | n)  = -(n | a) if n = a = 3 (mod 4) eles (n | a)
		a %= n;
	}
	if (n == 1) return res;
	else return 0;
}

int16_t legendre2(LNum a, LNum p) {
	int8_t res = 1;
	for (LNum f : factorization(p)) {
		res *= jacobi(a, f);
	}
	return res;
}

// Legendre symbol. Returns 1, 0, or p-1
LNum legendre1(LNum a, LNum p) {
	LNum res = a.pow_mod((p - 1) / 2, p);
	// assert(res == legendre2(a, p));
	return res;
}

tuple<LNum, LNum> mul(tuple<LNum, LNum> aa, tuple<LNum, LNum> bb, LNum p, LNum finalOmega) {
	return make_tuple(
		(get<0>(aa) * get<0>(bb) + get<1>(aa) * get<1>(bb) * finalOmega) % p,
		(get<0>(aa) * get<1>(bb) + get<0>(bb) * get<1>(aa)) % p
	);
}

tuple<LNum, LNum, bool> chipolli(LNum n, LNum p) {
	if (legendre1(n, p) != 1) {
		return make_tuple(0, 0, false);
	}

	LNum a = 0;
	LNum omega2 = 0;
	while (true) {
		omega2 = (a * a + p - n) % p;
		if (legendre1(omega2, p) == p - 1) {
			break;
		}
		a += 1;
	}

	// Step 2: Compute power
	tuple<LNum, LNum> r = make_tuple(1, 0);
	tuple<LNum, LNum> s = make_tuple(a, 1);
	LNum nn = ((p + 1) / 2) % p;
	while (nn > 0) {
		if (nn % 2 == 1) {
			r = mul(r, s, p, omega2);
		}
		s = mul(s, s, p, omega2);
		nn /= 2;
	}

	// Step 3: Check x in Fp
	if (get<1>(r) != 0) {
		return make_tuple(0, 0, false);
	}

	// Step 5: Check x * x = n
	if (get<0>(r)* get<0>(r) % p != n) {
		return make_tuple(0, 0, false);
	}

	// Step 4: Solutions
	return make_tuple(get<0>(r), p - get<0>(r), true);
}

uint64_t random(uint64_t a, uint64_t b) {
	return uniform_int_distribution<mt19937::result_type>(a, b)
		(
		(mt19937&)mt19937(
			random_device()()
		)
			);
}

LNum gcd(LNum a, LNum b) {
	while (b != 0) {
		a %= b;
		if (a == 0)
			return b;
		b %= a;
	}
	return a;
}

LNum ro_pollard(LNum N) {
	LNum a = N - 2;
	uint64_t b = numeric_limits<uint64_t>::max();

	LNum x = random(1, a < b ? a.to_int() : b);
	LNum y = 1;
	uint64_t i = 0;
	uint64_t stage = 2;
	while (gcd(N, x > y ? x - y : y - x) == 1) {
		if (i == stage) {
			y = x;
			stage = stage * 2;
		}
		x = (x * x - 1) % N;
		i = i + 1;
	}
	return gcd(N, x > y ? x - y : y - x);
}




int main() {
	LNum number = 10403, loop = 1, count = 0;
	LNum x_fixed = 2, x = 2, size = 2, factor = 0;

	do {
		printf("----   loop %4i   ----\n", loop);
		count = size;
		do {
			x = (x * x + 1) % number;
			factor = gcd(LNum::abs_sub(x, x_fixed), number);
			printf("count = %4i  x = %6i  factor = %i\n", size - count + 1, x, factor);
			count -= 1;
		} while (count > 0 && (factor == 1));
		size *= 2;
		x_fixed = x;
		loop = loop + 1;
	} while (factor == 1);
	printf("factor is %i\n", factor);

	//LNum big("1234567891011121314151617181920212223242526272829");
	//while (big > 1) {
	//	LNum d = ro_pollard(big);
	//	cout << d << ' ';
	//	big = big / d;
	//}
	//cout << endl;

	// GCD test
	//cout << gcd(LNum("1234567891011121314151617181920212223242526272829"), LNum("1221")) << endl;

	// Euler test
	//cout << "3^x === 13 (mod 17)\n";
	//cout << solve(3, 13, 17) << endl;
	//cout << "Euler (Totient) function: " << 
	//for (LNum n = 1; n <= 25; n += 1) {
	//	cout << "n=" << n << "\ttotient(n)=" << totient(n) << (totient(n) == n - 1 ? "\tprime" : "") << endl;
	//}
	//for (LNum i = 100; i <= 1000; i *= 10) {
	//	LNum res = 0;
	//	for (LNum j = 1; j <= i; j += 1) {
	//		if (totient(j) + 1 == j) res += 1;
	//	}
	//	cout << res << " primes below " << i << endl;
	//}

	// Mobius test
	//cout << mobius(1234891) << endl;

	// Legendre test
	/*cout << legendre1(30, 109) << endl;
	cout << legendre1(30, 127) << endl;*/

	// Jacobi test
	/*cout << jacobi(1001, 9907) << endl;
	cout << jacobi(19, 45) << endl;*/

	// Chipolli test
	//cout << get<0>(chipolli(LNum("34035243914635549601583369544560650254325084643201"), (LNum("10")^50) + 151));


	//cout << dl(3, 13, 17) << endl;

	//cout << LNum("24523748428").pow_mod(LNum("6500000"), LNum("98723459723")) << '\n';  //88398031434 3007310280
	//cout << "123456789876543212345678987654321 * 159753579515975357951: " << LNum("123456789876543212345678987654321") * LNum("159753579515975357951") << '\n';
	//cout << "sqrt(9^40): " << LNum("147808829414345923316083210206383297601").sqrt().to_str() << '\n';
	//cout << "9^20: " << (LNum("9")^20).to_str() << '\n';
	//cout << "10^20+1 > 10^20: " << (((LNum("10")^20) < LNum("10")^20 + 1) ? "true" : "false") << '\n';
	//cout << "1234567^1234: " << (LNum("1234567") ^ LNum("1234")) << '\n';


	// Chinese remainder test
	//cout << "x = 16 (mod 17)\nx = 22 (mod 23)\nx = 30 (mod 31)\n";
	//vector<LNum> n = { 17, 23, 31 };
	//vector<LNum> a = { 16, 22, 30 };
	//try {
	//	cout << chineseRemainder(n, a).to_str() << '\n' << endl;
	//}
	//catch (invalid_argument error) {
	//	cout << error.what() << "\n\n";
	//}
}

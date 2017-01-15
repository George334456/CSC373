"""
Modular exponentiation:
Given input a,b,m in natural numbers
Output (a ** b) mod m
"""
import math

def brute_force(a,b,m):
    """
    (int, int, int) -> (int)
    This is a brute force algorithm that will take a, and continuously multiply itself
    times until it hits b times updating it to be mod m each time
    and returning the final output.
    :param a: The base number. Needs to be greater than 0
    :param b: The exponentiation number.
    :param m: the modular base
    :return: a ** b mod m
    """
    """
    From [0,b). This is still "b" numbers.
    At each iteration, we increase k by one more factor of a.
    Thus, our loop invariant is k * a^(b-i) % m = a^b % m
    Initiation:
      k = 1, i = 0.
      (LHS):
      k * a ^ (b - i) % m
      (after substitution of initial values) -> 1 * a ^ (b - 0) % m
      = a ^ b % m, the RHS.

    Maintenance:
    Assume that at the j-th iteration, the loop invariant holds true
    We want to show that the j + 1-th iteration holds true
    @ j-th iteration, we have k * a ^ (b - j) % m = a ^ b % m
    Thus k = a ^ j % m. (Assuming the loop invariant holds true at the j-th iteration
    Then at the j + 1-th iteration, we have
    k * a % m(by the k *= a % m)
    Thus k = a ^ (j + 1) % m
    Then a ^ (b - i) % m at the j + 1-th iteration is a ^ (b - j - 1) % m
    Then k * a ^ (b - j - 1) % m @ the j + 1-th iteration after substituting k is
    a ^ (j + 1) * a ^ (b - j - 1) % m = a ^ b % m, holding the loop invariant
    Thus we maintain our loop invariant condition

    Termination:
    At termination, i = b
    Then k * a ^ (b - b) % m = k * a ^ 0 % m = k % m = a ^ b % m
    """
    k = 1
    for i in range(b):
        k *= a % m

    # Idea here is that we multiply a by itself b times.
    # Our "computation of interest" is how many times we perform a multiplication
    # Because a is multiplied by itself b times, this algorithm has
    # a run-time of O(b) time.

    return k % m


def repeated_squares(a,b,m):
    """
    (int, int, int) -> (int)

    Idea here is to go for "repeated squares".
    We in fact don't need to go up by one, but have to go up by powers of two!
    We can just multiply k by itself, getting us to move up in powers of 2.

    It is however, not complete as we will demonstrate, and we will need another trick
    :param a: The base number. Needs to be greater than 0
    :param b: The exponentiation number.
    :param m: the modular base
    :return: a ** b mod m
    """
    l = math.log(b,2)

    # This is the caveat: b must be a power of two for this to work
    # However, if it is a power of two, we can lower the run time down to just
    # log(b), because like the brute force approach, the run time of the algorithm
    # is the same as the number of times we execute the for loop, which we can see
    # is O(log_2 b)
    if not (l % 2 == 1.0 or l % 2 == 0.0):
        raise TypeError
    k = a % m
    # case when l = 0
    if l == 0:
        return 1
    for i in range(int(l)):
        k *= k % m
    return k % m


def repeated_squares_any(a,b,m):
    """
    (int, int, int) -> (int)

    We take the same idea as repeated squares and adapt it to any number b.
    We do this by looking at the binary representation of the number b.
    If the right most digit is 0, we shift right IE divide b by two (and in terms of
    doing this algorithm, we are squaring the number by itself
    If the right most digit is 1, we change it to 0 (in terms of this algorithm, we are
    just adding another factor of a % m)

    Ex: b = 23
    We will proceed by going like so: 23-> 22 -> 11 -> 10 -> 5 -> 4 -> 2 -> 1 -> 0
    Or in binary
    10111 -> 10110 -> 1011 -> 1010 -> 101 -> 100 -> 10 -> 1 -> 0

    :param a: The base number. Needs to be greater than 0
    :param b: The exponentiation number.
    :param m: the modular base
    :return: a ** b mod m
    """
    """
    Invariant: t * x ^ p % m = a ^ b % m
    Initiation:
    Before the loop runs, we have t = 1, x = a % m and p = b
    Then we have 1 * a ^ b % m = a ^ b % m

    Maintenance:
    We assume this loop invariant held for the j-th iteration.
    Then t * x ^ p % m = a ^ b % m
    On the next iteration, we then have two cases:
    case 1, p is odd.
        Then t * x * x ^ (p - 1) = t * x ^ p % m = a ^ b % m
    case 2, p is even
        Then t * (x ^ 2) ^ (p / 2) = t * x ^ p % m = a ^ b % m

    Termination:
    At termination, we have p = 0
    Then by the invariant, because we have proven that at initiation it works and as it
    goes forward, the loop invariant is held, we have at termination:
    t * x ^ p % m = a ^ b % m
    = t * x ^ 0 % m = a ^ b % m
    Meaning that t holds the value that we want.

    Run-time analysis:
    Like the above, we only care about the number of multiplications, so we just have to
    count the number of iterations this has.

    The key observation is to understand that for every 2 iterations, p is halved

    Thus, let p_i be value of p prior to i-th iteration

    p_1 = b
    p_(1 + 2) <= p_1/2 = b/2
    p_(1 + 2 + 2) <= p_(1+2) = b/4
    ...

    p_(1+2k) <= b/2^k
    Proof by induction:
    Base case: p_1 = b <= b
    Inductive hypothesis: p_(1+2k) <= b/2^k
    Inductive step:
    Assume Inductive hypothesis (IH)
    Prove for p_(1+2(k+1))
    p_(1+2(k+1)) = p_(1 + 2k + 2).
    Since p_(1 + 2k + 2) is 2 more iterations than p_(1 + 2k), we know that p is halved, then
    p_(1 + 2k + 2) <= p_(1 + 2k)/2 = (by IH) (b/2 ^ k) * (1/2) = (b/2^(k+1)).

    Thus p_(1+2k) <= b/2^k for all k in natural numbers

    Now, to look for when this will terminate, we need when p_(1+2k) < 1
    This will be guaranteed when b/2^k < 1 (since p_(1+2k) <= b/2^k)
    Thus k = floor(log_2(b)) + 1.
    This will then give us a running time of 1 + 2 * floor(log_2(b)) + 1, which is
    in O(log k) time.
    """
    t = 1
    x = a % m
    p = b
    while p > 0:
        if p % 2 == 1: # p is odd
            t = t * x % m
            p -= 1
        elif p % 2 == 0:
            x = x * x % m
            p /= 2
    return t % m

def main():
    a = brute_force(2,10,10)
    print(a)
    b = repeated_squares(2,64,10)
    print(b)
    c = brute_force(2,64,10)
    print(c)
    d = repeated_squares_any(2, 64, 10)
    print(d)
    # e = repeated_squares(2, 63, 10) #will fail
    f = brute_force(5, 10000, 10)
    print(f)
    g = repeated_squares_any(5, 10000, 10)
    print(g)

if __name__ == "__main__":
    main()
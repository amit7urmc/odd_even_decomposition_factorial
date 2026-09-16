from math import floor
import time
from functools import reduce
from itertools import starmap
from operator import mul
from collections import defaultdict, namedtuple
from csv import writer
from math import log, sqrt

returned_result = namedtuple('FactorialPrimeDecomposition', [
                             'Factorial', 'PrimeDecomposition', 'StoppingPrime', 'TimeTakenForDifferentSteps'])


def compute_fact_classic(n: int) -> int:
    """
    This function computes the factorial of n, in classical way.
    The numbers are iteratively multiplied to get the factorial
    """
    result = 1
    for i in range(1, n+1):
        result *= i
    return result


def odd_part(n: int, k: int) -> int:
    """
    This function computes the upper-limit of the product for a value of n
    and k (iteration number)
    """
    return floor((n/(2**k))+(1*(floor((n/(2**(k-1)))) % 2)))


def sieve_of_eratosthenes(n: int) -> list[int]:
    if n < 2:
        return []

    # Track primality using index (True = prime, False = composite)
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False

    # Mark multiples of primes starting from i^2
    for i in range(2, int(n**0.5) + 1):
        if is_prime[i]:
            for j in range(i * i, n + 1, i):
                is_prime[j] = False

    # Extract prime numbers
    return [num for num, prime in enumerate(is_prime) if prime]

def legendre_s_p_adic_valuation(n: int) -> dict[int, int]:
    primes = sieve_of_eratosthenes(n)
    p_adic_valuation = defaultdict(int)
    for prime in primes:
        power_ = 1
        exponent=floor(n/(prime**power_))
        while exponent:
            p_adic_valuation[prime] += exponent
            power_ += 1
            exponent=floor(n/(prime**power_))
    return p_adic_valuation
            
        

def compute_fact_primes_decomposition(n: int, suppress_final_factorial: bool = False) -> int:
    """
    This function computes the factorial as well as prime factors decomposition!
    Note: The minimum number for which factorial can be computed is 3!

    :param n: number for which factorial and prime decomposition is desired
    :type n: int
    :return: Named tuple of factorial and prime decomposition
    :rtype: int
    """

    # 1! and 2! are special for this algorithm so they are treated differently.
    if n == 1:
        return returned_result(1, None, None, 0)
    elif n == 2:
        return returned_result(2, {2: 1}, 2, 0)

    # Needed purely to speed up the lookup
    odd_num_index_dict = defaultdict(int)
    odd_num_list = []  # This list will have initially all the odd numbers. From this list prime numbers will emerge. The list structure gurantees the ordering
    # This list will have the exponents of each prime number in the odd_num_list.
    odd_num_exponent_list = []
    # All peeled off primes and their exponents will reside here.
    primes = defaultdict(int)
    even_power = 0
    k = 1
    # Step 1
    step_1_time = time.time()
    while (floor(n/(2**k)) >= 1):
        odd_upper_limit = odd_part(n, k)
        for odd_num in range(3, 2*odd_upper_limit+1, 2):
            if odd_num in odd_num_index_dict:
                index_odd_num = odd_num_index_dict.get(odd_num)
                odd_num_exponent_list[index_odd_num] += 1
            else:
                odd_num_index_dict[odd_num] = len(odd_num_exponent_list)
                odd_num_list.append(odd_num)
                odd_num_exponent_list.append(1)
        even_power += floor(n/(2**k))
        k += 1
    primes[2] = even_power
    step_1_time = time.time() - step_1_time
    # Step 2 (already achieved partially)
    # This list is needed for repeated division (Extraction of prime exponents)
    step_2_time = time.time()
    odd_num_list_raised = list(map(pow, odd_num_list, odd_num_exponent_list))
    step_2_time = time.time() - step_2_time
    # Step 3
    total_step_3_time = 0
    step_3_time = time.time()
    left_pointer = 0
    next_prime = odd_num_list[left_pointer]
    valid_step = next_prime != 1 and next_prime <= len(odd_num_list)
    step_3_time = time.time() - step_3_time
    total_step_3_time += step_3_time
    total_step_4_time, total_step_5_time = 0, 0
    while valid_step:
        step_3_time = time.time()
        primes[next_prime] = odd_num_exponent_list[left_pointer]
        valid_slots = range(left_pointer+next_prime,
                            len(odd_num_list), next_prime)
        step_3_time = time.time() - step_3_time
        total_step_3_time += step_3_time
        # Step 4 (Optimized: Direct Integer Division without divmod/tuple overhead)
        step_4_time = time.time()
        p = next_prime

        for slot in valid_slots:
            # Check if this slot still contains factors of p
            val_raised = odd_num_list_raised[slot]
            if val_raised > 1 and val_raised % p == 0:
                # Count how many powers of p are present in this specific slot
                # using fast integer floor division
                count = 0
                while val_raised % p == 0:
                    val_raised //= p
                    count += 1

                # Update state using the extracted factor count
                odd_num_list_raised[slot] = val_raised
                odd_num_exponent_list[slot] -= count
                primes[p] += count

        step_4_time = time.time() - step_4_time
        total_step_4_time += step_4_time
        # Step 5 (Optimized)
        step_5_time = time.time()

        # 1. Advance pointer to the next active candidate (value > 1)
        left_pointer += 1
        num_odd_items = len(odd_num_list)

        while left_pointer < num_odd_items and odd_num_list_raised[left_pointer] <= 1:
            left_pointer += 1

        # 2. Check termination condition without creating a list slice
        if left_pointer < num_odd_items:
            next_prime = odd_num_list[left_pointer]
            # Valid if next_prime <= remaining elements count: (num_odd_items - left_pointer)
            valid_step = next_prime <= (num_odd_items - left_pointer)
        else:
            valid_step = False

        step_5_time = time.time() - step_5_time
        total_step_5_time += step_5_time
    # Process the remaining prime numbers whose further decomposition is not desired.
    step_6_time = time.time()
    for prime_index, prime_exponent in enumerate(odd_num_exponent_list[left_pointer:], start=left_pointer):
        if prime_exponent < 1:  # i.e. All exponents have already been peeled off
            continue
        primes[odd_num_list[prime_index]] = prime_exponent
    step_6_time = time.time() - step_6_time
    step_7_time = time.time()
    if not suppress_final_factorial:
        factorial = reduce(mul, starmap(pow, ((k, v) for k, v in primes.items())))
    else:
        factorial = None
    step_7_time = time.time() - step_7_time

    times = [step_1_time , step_2_time , step_3_time , total_step_4_time , total_step_5_time , step_6_time , step_7_time]
    time_dict = {}
    for i, time_taken in enumerate(times):
        time_dict[f"step_{i+1}_time"] = time_taken/sum(times)*100.0
    # Return primes and exponents, stopping prime and also the factorial
    return returned_result(factorial, dict(primes), next_prime, time_dict)


if __name__ == "__main__":
    with open("GrowthSummaryTimeSplit.csv", "w") as opened_file_handle:
        p_writer = writer(opened_file_handle)
        row_headers = ['n',
                       'Stopping Prime',
                       'Classical Time',
                       'Recursive Decomposition',
                       'Remainder After 3x',
                       'LN(N)',
                       'RatioNwithStoppingPrime',
                       'Legendres Method Time',
                       'Recursive Method Time']
        p_writer.writerow(row_headers)
        n_values = [1, 2, 3, 4, 5, 7, 9, 11, 15, 19, 29, 35, 43, 50, 101, 251, 500, 1013, 2003, 4001, 10009, 16067, 25000, 50021, 64000, 100003, 126719, 250000, 500057, 750019, 1000000]
        for n_index, n_value in enumerate(n_values):
            print(f"Calculating Factorials and p-adic valuation for {n_value}!")
            t_classic_start = time.perf_counter()
            classic_fact = compute_fact_classic(n_value)
            t_classic = time.perf_counter() - t_classic_start

            t_recursive_decomposition_start = time.perf_counter()
            recursive_decomposition_fact = compute_fact_primes_decomposition(n_value)
            t_recursive_decomposition = time.perf_counter() - t_recursive_decomposition_start
            print("Checking if the classic and recursive decomposition methods agree", end=".....")
            assert classic_fact == recursive_decomposition_fact.Factorial, "The agreement between classic and recursive decomposition method failed"
            print("Passed", end="\n")
            legendres_time, recursive_time = None, None
            if n_value > 1:               
                start_time = time.time()
                classic_legendre_s_valuation = legendre_s_p_adic_valuation(n_value)
                legendres_time = time.time()-start_time
                print(f"Legendre's method took {legendres_time}")
                start_time = time.time()
                recursive_legendre_s_valuation = compute_fact_primes_decomposition(n_value, suppress_final_factorial=True).PrimeDecomposition
                recursive_time = time.time()-start_time 
                print(f"Recursive method took {recursive_time}")
                print("Now checking for a match with p-adic valuation between two methods", end="......")
                assert len(classic_legendre_s_valuation) == len(recursive_legendre_s_valuation), "The number of primes differ between two methods"
                assert len(set(classic_legendre_s_valuation.keys()).difference(set(recursive_legendre_s_valuation.keys()))) == 0, "At least one prime number is different between two methods"
                for prime in set(classic_legendre_s_valuation.keys()):
                    assert classic_legendre_s_valuation[prime] == recursive_legendre_s_valuation[prime], "At least one exponent of a prime number is different"
                print("Passed", end="\n")
                    
            ## The ratio between n and stopping Prime tends to a value of 3.
            ## We want to see remainder, stopping-prime and the ratios
            stopping_prime = recursive_decomposition_fact.StoppingPrime
            remainder = 3 * stopping_prime - n_value if stopping_prime else None

            print("Writing to CSV file", end=".....")
            row = [n_value,
                   recursive_decomposition_fact.StoppingPrime,
                   t_classic,
                   t_recursive_decomposition,
                   remainder,
                   log(n_value),
                   n_value/stopping_prime if stopping_prime else None, ## This value tends to 3
                   legendres_time,
                   recursive_time
                   ]
            p_writer.writerow(row)
            opened_file_handle.flush()
            print("Written to CSV file", end="\n")
            print(f"Time taken breakup for different steps is {recursive_decomposition_fact.TimeTakenForDifferentSteps}")
            print()

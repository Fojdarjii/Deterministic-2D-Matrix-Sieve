import time

def dynamic_2d_matrix_sieve(limit):
    start_time = time.time()
    
    # 1. Horizontal candidate generation (6k +/- 1)
    candidates = set()
    for k in range(1, limit // 6 + 2):
        num1 = 6 * k - 1
        num2 = 6 * k + 1
        if 11 <= num1 <= limit: candidates.add(num1)
        if 11 <= num2 <= limit: candidates.add(num2)
            
    # 2. Vertical multiplier grid setup
    vertical_multipliers = [n for n in sorted(list(candidates)) if n * n <= limit]
    
    # 3. Coordinate intersection mapping (Candidate x Candidate)
    cheaters = set()
    for c1 in vertical_multipliers:
        for c2 in sorted(list(candidates)):
            prod = c1 * c2
            if prod <= limit:
                cheaters.add(prod)
            else:
                break
                
    # 4. Final difference filtration for primes and twin pairs
    pure_primes = candidates - cheaters
    twin_count = 0
    sorted_primes = sorted(list(pure_primes))
    
    for idx in range(len(sorted_primes) - 1):
        if sorted_primes[idx+1] - sorted_primes[idx] == 2:
            twin_count += 1

    print(f"Limit: {limit}")
    print(f"Candidates Tested: {len(candidates)}")
    print(f"Composites Identified: {len(cheaters)}")
    print(f"Twin Prime Pairs: {twin_count}")
    print(f"Execution Window: {time.time() - start_time:.4f}s")

if __name__ == "__main__":
    dynamic_2d_matrix_sieve(10000000)

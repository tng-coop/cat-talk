import sys

# ==========================================
# 0. THE PROBLEM: UNIVERSE-SIZED NUMBERS
# ==========================================
# Real Godel numbers like 2^(3^(5^...)) are too big for RAM.
# We solve this by creating a "Virtual Number" class.
# It acts like an integer but stores its prime factors tree.
# This lets us do "Division" instantly by looking up the map.

class GodelNumber:
    def __init__(self, value=None, factors=None):
        if factors is not None:
            self.factors = factors  # Dictionary {prime: exponent}
            self.is_virtual = True
            self.raw_value = None
        else:
            self.raw_value = value
            self.is_virtual = False
            self.factors = {}

    def __repr__(self):
        if not self.is_virtual:
            return str(self.raw_value)
        return f"Virtual({len(self.factors)} factors)"

    def get_exponent_at_prime(self, p):
        """
        ARITHMETIC OPERATION: DIVISION / FACTORIZATION
        Conceptually: returns (self / p^k) % p == 0 logic
        Actually: Look up the exponent in our tree.
        """
        if not self.is_virtual:
            # Factorize real small integer
            n = self.raw_value
            count = 0
            while n > 0 and n % p == 0:
                count += 1
                n //= p
            return GodelNumber(count)
        
        # Virtual lookup
        return self.factors.get(p, GodelNumber(0))

    def to_list(self):
        """Debug helper to show the sequence [n1, n2, n3]"""
        if not self.is_virtual:
            # Decoding a raw integer is basic
            return [] # simplifaction
        
        # For virtual numbers, we just read primes 2, 3, 5...
        res = []
        for p in PRIMES:
            if p not in self.factors: break
            res.append(self.factors[p])
        return res

    def __eq__(self, other):
        """ARITHMETIC OPERATION: EQUALITY CHECK"""
        if isinstance(other, int):
            return not self.is_virtual and self.raw_value == other
        
        if self.is_virtual != other.is_virtual:
            return False
        
        if not self.is_virtual:
            return self.raw_value == other.raw_value
            
        # Compare factor trees deeply
        all_primes = set(self.factors.keys()) | set(other.factors.keys())
        for p in all_primes:
            exp1 = self.factors.get(p, GodelNumber(0))
            exp2 = other.factors.get(p, GodelNumber(0))
            if exp1 != exp2:
                return False
        return True


# ==========================================
# 1. THE HARDWARE
# ==========================================
SYMBOL_CODES = {
    '0': 1, 'S': 3, '=': 5, '¬': 7,
    '(': 13, ')': 15, 'v': 17,
    '->': 21
}
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

# ==========================================
# 2. THE COMPILER
# ==========================================
def encode_sequence_virtual(items):
    """
    Takes a list of items (either GodelNumbers or ints).
    Returns a Virtual GodelNumber representing 2^item1 * 3^item2 ...
    """
    factors = {}
    for i, item in enumerate(items):
        if i >= len(PRIMES): break # Demo limit
        p = PRIMES[i]
        # Ensure item is GodelNumber
        if isinstance(item, int):
            item = GodelNumber(item)
        factors[p] = item
    return GodelNumber(factors=factors)

def encode_formula_str(s):
    tokens = []
    i = 0
    while i < len(s):
        if s[i:i+2] == '->':
            tokens.append('->')
            i += 2
        elif s[i] in SYMBOL_CODES:
            tokens.append(s[i])
            i += 1
        else:
            i += 1
    
    codes = [SYMBOL_CODES[t] for t in tokens]
    # Simple formulas are small enough to be raw integers usually,
    # but let's make them virtual to be consistent and robust.
    return encode_sequence_virtual(codes)

# ==========================================
# 3. THE COLLISION LOGIC
# ==========================================
def glue_numbers_with_arrow_symbol(n_a, n_b):
    """
    Builds the 'Expected Number' for A -> B.
    CRITICAL: This does NOT 'understand' implication.
    It just GLUES three lists together: [A] + [21] + [B].
    """
    # 1. Extract lists (Division)
    seq_a = n_a.to_list()
    seq_b = n_b.to_list()
    
    # 2. Combine (The 'Gluing')
    # 21 is just the code for '->'. It has no logical meaning to the machine,
    # it is just a separator token like a comma.
    arrow_code = SYMBOL_CODES['->']
    
    # print(f"    [ARITHMETIC OP] Concatenating: List A + [21] + List B") 
    
    new_seq = seq_a + [arrow_code] + seq_b
    
    # 3. Build new Virtual Number
    return encode_sequence_virtual(new_seq)

# ==========================================
# 4. THE PROOF CHECKER
# ==========================================
def check_proof(proof_P):
    print("\n--- CHECKING VIRTUAL PROOF ---")
    
    # 1. DECODE (Extract factors from the virtual tree)
    # proof_P is 2^n1 * 3^n2 ... we want [n1, n2, n3]
    steps = proof_P.to_list()
    print(f"Decoded {len(steps)} steps.")
    
    valid_steps_so_far = []
    
    for i, step_num in enumerate(steps):
        print(f"\nVerifying Step {i+1}...")
        
        is_valid = False
        reason = ""
        
        # Check Axiom 0=0
        axiom1 = encode_formula_str("0=0")
        if step_num == axiom1:
            is_valid = True
            reason = "Matches Axiom '0=0'"
            
        # Check Axiom 2
        axiom2 = encode_formula_str("0=0->S(0)=S(0)")
        if step_num == axiom2:
            is_valid = True
            reason = "Matches Axiom '0=0->S(0)=S(0)'"
            
        # Check Modus Ponens
        if not is_valid:
            print(f"  [DEBUG] Not an axiom. Checking if derived via Modus Ponens...")
            for idx, prev_p in enumerate(valid_steps_so_far):
                # We want to check if "prev_p -> step_num" exists in our valid steps.
                # 1. Hypothesize the Link
                print(f"    - Checking hypothesis: Does Step {idx+1} imply Step {i+1}?")
                
                # 2. Construct the logical number for "Step A -> Step B"
                # REPLACED FUNCTION CALL HERE
                test_link = glue_numbers_with_arrow_symbol(prev_p, step_num)
                # (In a real debug, we might print the massive number, but here we trust the object)
                
                # 3. Search for this number
                found_at = -1
                for k, link_candidate in enumerate(valid_steps_so_far):
                    if link_candidate == test_link:
                        found_at = k
                        break
                        
                if found_at != -1:
                    print(f"      [MATCH] FOUND! Step {found_at+1} is exactly 'Step {idx+1} -> Step {i+1}'")
                    is_valid = True
                    reason = f"Derived via Modus Ponens (Found link at Step {found_at+1})"
                    break
                else:
                    print(f"      [NO MATCH] No step found that looks like 'Step {idx+1} -> Step {i+1}'")
        
        if is_valid:
            print(f"  [PASS] {reason}")
            print(f"  [ACTION] Step {i+1} is now accepted as a PROVEN TRUTH.")
            print(f"           It can now be used to verify future steps.")
            valid_steps_so_far.append(step_num)
        else:
            print(f"  [FAIL] Step {step_num} is not an axiom and not derived.")
            return False

    print("\n[RESULT] PROOF IS VALID.")
    print("         The system confirms: 'S(0)=S(0)' follows arithmetically from '0=0'.")
    return True

# ==========================================
# 5. DEMO
# ==========================================
if __name__ == "__main__":
    print("Constructing Proof Steps (as Virtual Trees)...")
    n1 = encode_formula_str("0=0")
    n2 = encode_formula_str("0=0->S(0)=S(0)")
    n3 = encode_formula_str("S(0)=S(0)")
    
    print("Packing Proof Number P...")
    proof_P = encode_sequence_virtual([n1, n2, n3])
    
    check_proof(proof_P)

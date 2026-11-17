import GSTOrderedNilpotentDressing

/-!
# All-order explicit conjugacy of nearby idempotents

Uncompiled proof draft. The difference itself may be nilpotent; no commutation
between the two idempotents is requested. This contains the old first-order
tangent conjugacy as a special case, and preserves actual image modules.
-/

namespace GSTNilpotentProjectionConjugacy
variable {R : Type*} [Ring R]

def bridge (p q : R) : R := q*p+(1-q)*(1-p)

theorem bridge_difference (p q : R) (hp : p*p=p) :
    bridge p q=1+(q-p)*(2*p-1) := by
  calc
    bridge p q=1-q-p+2*(q*p) := by unfold bridge; noncomm_ring
    _ = 1+(q-p)*(2*p-1) := by
      symm
      calc
        1+(q-p)*(2*p-1)=1-q+p+2*(q*p)-2*(p*p) := by noncomm_ring
        _ = 1-q-p+2*(q*p) := by rw [hp]; noncomm_ring

theorem bridge_intertwines (p q : R) (hp : p*p=p) (hq : q*q=q) :
    bridge p q*p=q*bridge p q := by
  have hl : bridge p q*p=q*p := by
    unfold bridge
    have hw : (1-p)*p=0 := by rw [sub_mul, one_mul, hp, sub_self]
    rw [add_mul, mul_assoc, hp, mul_assoc, sub_mul, one_mul, hw, mul_zero,
      sub_self, add_zero]
  have hr : q*bridge p q=q*p := by
    unfold bridge
    have hzq : q*(1-q)=0 := by rw [mul_sub, mul_one, hq, sub_self]
    rw [mul_add, ← mul_assoc, hq, ← mul_assoc, mul_sub, mul_one, hzq,
      zero_mul, sub_self, add_zero]
  exact hl.trans hr.symm

theorem bridge_product (p q : R) (hp : p*p=p) (hq : q*q=q) :
    bridge p q*bridge q p=1-(q-p)^2 := by
  have hz : p*(1-p)=0 := by rw [mul_sub, mul_one, hp, sub_self]
  have hw : (1-p)*p=0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hc : (1-p)*(1-p)=1-p := by
    calc
      (1-p)*(1-p)=1-p-p+p*p := by noncomm_ring
      _ = 1-p := by rw [hp]; noncomm_ring
  unfold bridge
  calc
    (q*p+(1-q)*(1-p))*(p*q+(1-p)*(1-q)) =
        q*(p*p)*q+q*(p*(1-p))*(1-q)+
          (1-q)*((1-p)*p)*q+(1-q)*((1-p)*(1-p))*(1-q) := by noncomm_ring
    _ = q*p*q+(1-q)*(1-p)*(1-q) := by rw [hp,hz,hw,hc]; noncomm_ring
    _ = 1-p-2*q+q*p+p*q+q*q := by noncomm_ring
    _ = 1-(q-p)^2 := by
      rw [hq]
      symm
      calc
        1-(q-p)^2=1-q*q+q*p+p*q-p*p := by noncomm_ring
        _ = 1-p-2*q+q*p+p*q+q := by rw [hp,hq]; noncomm_ring

/-- A two-sided unit can be built from separate left and right inverse data. -/
def unitFromTwoInverses (u L S : R) (hL : L*u=1) (hS : u*S=1) : Rˣ where
  val := u
  inv := S
  val_inv := hS
  inv_val := by
    have heq : S=L := by
      calc
        S=(L*u)*S := by rw [hL,one_mul]
        _ = L*(u*S) := mul_assoc _ _ _
        _ = L := by rw [hS,mul_one]
    rw [heq,hL]

def bridgeUnit (p q : R) (hp : p*p=p) (hq : q*q=q)
    (n : ℕ) (hd : (q-p)^n=0) : Rˣ := by
  have hsquare : ((q-p)^2)^n=0 := by
    calc
      ((q-p)^2)^n=((q-p)^n)^2 := by simp only [← pow_mul, Nat.mul_comm 2 n]
      _ = 0 := by rw [hd]; norm_num
  have hneg : (-((q-p)^2))^n=0 := by rw [neg_pow,hsquare,mul_zero]
  let z := GSTOrderedNilpotentDressing.unitOfNilpotent (-((q-p)^2)) n hneg
  have hz : (z : R)=1-(q-p)^2 := by simp [z,GSTOrderedNilpotentDressing.unitOfNilpotent,sub_eq_add_neg]
  let v := bridge q p
  have huv : bridge p q*v=(z : R) := by rw [bridge_product p q hp hq]; exact hz.symm
  have hvu : v*bridge p q=(z : R) := by
    rw [bridge_product q p hq hp]
    rw [hz]
    noncomm_ring
  exact unitFromTwoInverses (bridge p q) ((↑(z⁻¹) : R)*v) (v*(↑(z⁻¹) : R))
    (by rw [mul_assoc,hvu]; exact z.inv_val)
    (by rw [← mul_assoc,huv]; exact z.val_inv)

@[simp] theorem bridgeUnit_value (p q : R) (hp : p*p=p) (hq : q*q=q)
    (n : ℕ) (hd : (q-p)^n=0) : (bridgeUnit p q hp hq n hd : R)=bridge p q := rfl

theorem bridgeUnit_conjugates (p q : R) (hp : p*p=p) (hq : q*q=q)
    (n : ℕ) (hd : (q-p)^n=0) :
    (bridgeUnit p q hp hq n hd : R)*p*(↑((bridgeUnit p q hp hq n hd)⁻¹) : R)=q := by
  let u := bridgeUnit p q hp hq n hd
  have hi : (u : R)*p=q*(u : R) := bridge_intertwines p q hp hq
  change (u : R)*p*(↑(u⁻¹) : R)=q
  have hinv : ((u : R) * ((u⁻¹ : Rˣ) : R)) = 1 := u.val_inv
  rw [hi,mul_assoc,hinv,mul_one]

#print axioms bridge_product
#print axioms bridgeUnit_conjugates
end GSTNilpotentProjectionConjugacy

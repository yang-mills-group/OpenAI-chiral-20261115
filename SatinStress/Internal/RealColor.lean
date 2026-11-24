import SatinStress.Internal.Flavor
import YM.CF.Reef.Ice
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open SU Gauge Matrix Finset Function
open Complex (I)
open scoped Matrix Kronecker Topology BigOperators

abbrev rays := Reef.frolic
lemma turnColor (u : Col) : embedC (rays u) = cc (embedC u) := Reef.fizz _
lemma rays_back (u : Col) : rays (rays u) = u := Reef.fiz2 _

lemma star_gen (Y : Fund) : star (ExTwo.gen Y)= ExTwo.gen (star Y) := by
  ext i j; simp [gen_entry,Matrix.one_apply, apply_ite (star:ℂ→ℂ),eq_comm,mul_comm,add_comm]
lemma cc_gen (Y : Fund) : cc (ExTwo.gen Y)= ExTwo.gen (cc Y) := by
  ext i j; simp [gen_entry,Matrix.one_apply,apply_ite (star:ℂ→ℂ),mul_comm]
lemma skew_gen (Y : Col) : star (upper (embedC Y)) = -upper (embedC Y) := by
  unfold upper; rw [star_gen,embedC_skew]; ext i j; simp [gen_entry]; abel
lemma skew_lower (Y : Col) : star (lower (embedC Y)) = -lower (embedC Y) := by
  unfold lower; rw [star_neg]; congr 1; apply Matrix.ext; intro i j
  exact Matrix.ext_iff.mpr (embedC_skew Y) j i -- tune swapped orientation
lemma cc_lower (Y : Fund) : cc (lower Y) = lower (cc Y) := by ext; simp [lower]

lemma selected_cc (a b : ℂ) (c : Col) : cc (selected a b (rays c)) = selected (star a) (star b) c := by
  simp only [selected_at,scheme,LinearMap.coe_mk,AddHom.coe_mk]
  have he(A : Op Ten)(B: Op F) : cc (Join.both A B) = Join.both (cc A) (cc B) := by ext i j; cases i <;> cases j <;> simp [Join.both]
  rw [turnColor,he,cc_smul,cc_smul,upper,cc_gen,cc_cc,cc_lower,cc_cc]; rfl
lemma selected_star (a b : ℂ) (c : Col) : star (selected a b c) = -selected (star a) (star b) c := by
  simp only [selected_at,scheme,LinearMap.coe_mk,AddHom.coe_mk,Join.star_both,star_smul,skew_gen,skew_lower]
  ext i j; cases i <;> cases j <;> simp [Join.both]
lemma ocean_star (a b) (u : Col) : star (ocean a b u) = -ocean (star a) (star b) u := by
  apply parts_ext; intro i j; change star (selected (a j i) (b j i) u) = - selected (star (a j i)) (star (b j i)) u; exact selected_star ..
lemma ocean_cc (a b) (u : Col) : cc (ocean a b (rays u))=ocean (cc a) (cc b) u := by
  apply parts_ext; intro i j; change cc (selected (a i j) (b i j) (rays u)) = selected (star (a i j)) (star (b i j)) u; exact selected_cc ..
-- U1 Improper motion formula
lemma flip_cc {n:Type*}[Fintype n][DecidableEq n] (A:Op n) : star (cc A)=Aᵀ := by ext i j; simp [cc]
lemma pay_x (a b) (u : Col) : (ocean a b (rays u))ᵀ = -ocean aᵀ bᵀ u := by
  rw [← flip_cc, ocean_cc,ocean_star, flip_cc, flip_cc]
lemma pay_phi (a b) : (pool a b)ᵀ=pool aᵀ bᵀ := by rw [← flip_cc,pool_cc, ← pool_star,flip_cc,flip_cc]

-- Full reduction using same Color (& normalize to `dMatter` on appropriate projections).
lemma charge_value (x) : ocean 1 1 x=dMatter (embedC x) := by
  apply parts_ext; intro i j; rw [← section_price, section_ocean, dMatter, part_tensor]
  by_cases t:i=j
  · simp [one_apply,t,selected_generator]
  simp [one_apply,t]

-- Present Linear map equivalences.
def pure_space : Submodule ℂ Piece where
  carrier := Pure
  add_mem' x y a := by simp only [mul_add,add_mul,x a,y a]
  smul_mem' c x hx u := by
    change _ * (c • x)=_; rw [Matrix.mul_smul, Matrix.smul_mul,hx]
  zero_mem' u := by simp

def mixed_space : Submodule ℂ (Col →ₗ[ℝ] Piece) where
  carrier := Mixed
  add_mem' {x y} hx hy t u := by simp only [LinearMap.add_apply,add_mul,mul_add,hx t u,hy t u] -- simp misuse `t`
  smul_mem' c x hx t u := by simp only [LinearMap.smul_apply,Matrix.mul_smul,Matrix.smul_mul,hx t u]
  zero_mem' _ _ := by simp

def pLaw : Submodule ℂ Piece where
  carrier x := x∈pure_space ∧ FixedFlavor x
  add_mem' x y := ⟨pure_space.add_mem x.1 y.1,fun g => by simp only [mul_add,add_mul,x.2 g,y.2 g]⟩
  smul_mem' c x hx := ⟨pure_space.smul_mem _ hx.1,fun u => by rw [Matrix.mul_smul, Matrix.smul_mul,hx.2]⟩
  zero_mem' := ⟨pure_space.zero_mem,fun _ => by simp⟩

def mLaw : Submodule ℂ (Col →ₗ[ℝ] Piece) where
  carrier x := x∈mixed_space ∧ ∀ i, FixedFlavor (x i)
  add_mem' x y := ⟨mixed_space.add_mem x.1 y.1,fun i g => by simp only [LinearMap.add_apply,mul_add,add_mul,x.2 i g,y.2 i g]⟩
  smul_mem' c x hx := ⟨mixed_space.smul_mem c hx.1,fun i g => by simp only [LinearMap.smul_apply,Matrix.mul_smul,Matrix.smul_mul,hx.2 i g]⟩
  zero_mem' := ⟨mixed_space.zero_mem,fun i g => by simp⟩

def families : (Op Age × Op Age) →ₗ[ℂ] pure_space where
  toFun z := ⟨pool z.1 z.2,pure_pool _ _⟩
  map_add' _ _ := Subtype.ext (pool_add ..)
  map_smul' _ _ := Subtype.ext (pool_smul ..)
def familiesM : (Op Age × Op Age) →ₗ[ℂ] mixed_space where
  toFun z := ⟨_,ocean_mixed z.1 z.2⟩
  map_add' _ _ := Subtype.ext (ocean_add ..)
  map_smul' _ _ := Subtype.ext (ocean_smul ..)

def binP : (Op Age × Op Age) ≃ₗ[ℂ] pure_space := LinearEquiv.ofBijective families (by
  constructor
  · exact fun _ _ h => Prod.ext_iff.mpr (pool_injective (congr_arg Subtype.val h))
  rintro ⟨x,hx⟩; obtain ⟨a,b,rfl⟩ := (purity _).mp hx; exact ⟨(a,b), rfl⟩ )
def binM : (Op Age × Op Age) ≃ₗ[ℂ] mixed_space := LinearEquiv.ofBijective familiesM (by
  constructor
  · exact fun _ _ h => Prod.ext_iff.mpr (ocean_injective (congr_arg Subtype.val h))
  rintro ⟨x,hx⟩; obtain ⟨a,b,rfl⟩ := (mixed_pool _).mp hx; exact ⟨(a,b), rfl⟩ )

private def simpleQ : (ℂ × ℂ) →ₗ[ℂ] Op Age × Op Age where
  toFun z := (z.1 • 1,z.2 • 1)
  map_add' _ _ := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]
lemma simple_unique : Injective (fun z : ℂ × ℂ => (z.1 • (1:Op Age), z.2 • (1:Op Age))) := by
  intro x y h; apply Prod.ext
  · simpa using Matrix.ext_iff.mpr (congr_arg Prod.fst h) 0 0
  simpa using Matrix.ext_iff.mpr (congr_arg Prod.snd h) 0 0

def kP : (ℂ × ℂ) →ₗ[ℂ] pLaw := (((pure_space.subtype).comp binP.toLinearMap).comp simpleQ).codRestrict _ (fun t =>
  (show Pure _ ∧ FixedFlavor _ from (invariantP _).mpr ⟨t.1,t.2,rfl⟩))
def kM : (ℂ × ℂ) →ₗ[ℂ] mLaw := (((mixed_space.subtype).comp binM.toLinearMap).comp simpleQ).codRestrict _ (fun t =>
  (show Mixed _ ∧ _ from (invariantM _).mpr ⟨t.1,t.2,rfl⟩))

def invariantPH : (ℂ × ℂ) ≃ₗ[ℂ] pLaw := LinearEquiv.ofBijective kP (by
  constructor
  · exact fun _ _ e => simple_unique (Prod.ext_iff.mpr (pool_injective (congr_arg Subtype.val e)))
  rintro ⟨x,hx⟩; obtain ⟨a,b,rfl⟩ := (invariantP _).mp hx; exact ⟨(a,b), rfl⟩ )
def invariantX : (ℂ × ℂ) ≃ₗ[ℂ] mLaw := LinearEquiv.ofBijective kM (by
  constructor
  · exact fun _ _ e => simple_unique (Prod.ext_iff.mpr (ocean_injective (congr_arg Subtype.val e)))
  rintro ⟨x,hx⟩; obtain ⟨a,b,rfl⟩ := (invariantM _).mp hx; exact ⟨(a,b), rfl⟩ )
lemma invariantRealPH (a b:ℝ) : cc (invariantPH ((a:ℂ),(b:ℂ))).val=(invariantPH (a,b)).val := by
  change cc (pool _ _)=(pool _ _); simp [pool_cc,simpleQ]
lemma invariantRealX (a b:ℝ) (u : Col) : cc ((invariantX ((a:ℂ),(b:ℂ))).val (rays u))=(invariantX (a,b)).val u := by
  change cc (ocean _ _ _)=(ocean _ _ _); rw [ocean_cc]; simp [simpleQ]
end YM.CF.SatinStressData

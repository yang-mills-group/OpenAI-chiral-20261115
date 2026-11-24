import YM.CF.Fir.Muff
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset
open scoped Topology Matrix BigOperators
variable (j:ℕ) (N:Side)
def bGraph (p:Momentum) := (gD p)⁻¹ • sine p
def mixL (p:Momentum) : Momentum := (N.val:ℂ)⁻¹ • ∑ l : Site N, muff j N (aliasAt p l)^2 • bGraph (aliasAt p l)
def extras (p:Momentum) : Momentum := (N.val:ℂ)⁻¹ • ∑ l∈univ.erase (0:Site N), muff j N (aliasAt p l)^2 • bGraph (aliasAt p l)
def bloom (p:Momentum) := muff j N (narrow N p)^2
def prodM (p q : Momentum) := ∑ a : Axis, p a*q a
def mass (p : Momentum) := D N p*(1+prodM (extras j N p) (extras j N p))+2*bloom j N p*prodM (ds N p) (extras j N p)+(bloom j N p)^2*Cminus N p
def shell (p:Momentum) := D N p/(mass j N p)
def skin (p:Momentum) := (mass j N p)⁻¹ • (bloom j N p • ds N p+D N p • extras j N p)
lemma mix_com (p:Momentum) : mixL j N p= extras j N p + (bloom j N p*(D N p)⁻¹) • ds N p := by
  unfold mixL extras; set f := fun l:Site N=> muff j N (aliasAt p l)^2 • bGraph (aliasAt p l)
  change _ • (∑ i,f i)= _ • (∑ i∈_,f i)+_
  rw [← sum_erase_add _ f (mem_univ (0:Site N)),smul_add]; congr 1
  ext a:1; simp only [f,alias_zero_eq,D,bloom,bGraph,ds,Pi.smul_apply,smul_eq_mul,mul_inv]; unfold narrow; field_simp
-- without gD ne field_simp problematic
lemma denom (p:Momentum) : D N p*(1+prodM (mixL j N p) (mixL j N p))=mass j N p ∨ D N p=0 := by
  by_cases h:D N p=0
  · exact Or.inr h
  left; rw [mix_com]; unfold mass
  let f:=extras j N p; let g:= ds N p; let b:= bloom j N p*(D N p)⁻¹
  change D N p *(1+prodM (f+b • g) (f+b • g))=_
  have he : prodM g g=D N p*Cminus N p := by simpa only [g,prodM,sq] using ds_sq N p -- `prodM` ds
  rw [show prodM (f+b • g) (f+b • g) = prodM f f+2*b*prodM g f+b^2*prodM g g by
    unfold prodM; rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; change (f i+b*g i)*(f i+b*g i)=_; ring]
  rw [he]; unfold b f g; field_simp; ring
lemma phys_bGraph (p:Momentum)(hp:physical p): physical (bGraph p):=by
  rw [← pq p hp]; unfold bGraph gD physical
  rw [r_real,wave_eq,star_smul,star_inv₀]
  simp [show ∀ y, sine (tmap y)= tmap (fun i=> Real.sin (y i)) from (fun y=> funext fun i=> by simp [sine,tmap]),show ∀ y,star (tmap y)=_ from tmap_physical]
lemma phys_mix (hN:Odd N.val)(p:Momentum)(hp:physical p): physical (mixL j N p):=by
  unfold mixL physical; rw [star_smul,star_inv₀,star_natCast,star_sum]
  simp only [star_smul,star_pow,muff_real j N hN _ (alias_real hp _), show ∀ l:Site N, star (bGraph (aliasAt p l))=_ from (fun l=>phys_bGraph _ (alias_real hp l))]
lemma noGhost {p:Momentum}(hp:p ∈ realCube zone)(h:p≠0) : (D N p).re>0 := (lt_of_lt_of_le (mul_pos (by norm_num) (lt_of_lt_of_le (mul_pos (pow_pos meter.low_pos 2) (lengthSq_pos h)) (divisor_real_bounds N hp).1)) (D_lower N hp.1)) -- constants
lemma prodM_self (p:Momentum)(hp:physical p) : prodM p p=((∑ i, (p i).re^2 : ℝ):ℂ):=by
  unfold prodM; push_cast; exact Finset.sum_congr rfl fun i _=> by conv_rhs => rw [show (((p i).re:ℝ):ℂ)=p i from congr_fun (pq p hp) i]; rw [sq]
lemma phys_D {p:Momentum}(hp:physical p) : (D N p).im=0:=by
  rw [D,gD,← pq _ (na_phys _ hp), r_real,wave_eq]; norm_cast
lemma mass_price (hN:Odd N.val){p:Momentum}(hp:p ∈ realCube zone)(h:p≠0) : (D N p).re≤ (mass j N p).re := by
  have he := noGhost N hp h
  rw [← (denom j N p).resolve_right (by intro hy; rw [hy] at he; exact lt_irrefl 0 he), prodM_self _ (phys_mix j N hN _ hp.1),Complex.mul_re]
  simp only [Complex.add_re,Complex.one_re, Complex.add_im, Complex.one_im, Complex.ofReal_re,Complex.ofReal_im,add_zero,mul_zero,sub_zero];
  exact le_mul_of_one_le_right he.le (le_add_of_nonneg_right (sum_nonneg fun i _=> sq_nonneg _))
@[simp] lemma mass_origin : mass j N 0= _root_.OfNat.ofNat 2 := by norm_num [mass,D,Cminus,prodM,gD,rad,mag,kin,pl,sine,narrow,bloom,ds]
lemma skin_def (p:Momentum): skin j N p=(shell j N p) • mixL j N p ∨ D N p=0 := by
  by_cases h:D N p=0
  · exact Or.inr h
  left; rw [skin,mix_com,shell]; ext i:1; simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,div_eq_mul_inv]; ring_nf -- edit
  rw [mul_assoc _ (D N p) ((D N p)⁻¹), mul_inv_cancel₀ h, mul_one]
end YM.CF.Fir

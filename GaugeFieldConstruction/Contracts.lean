import GaugeFieldConstruction.Buttons

/-!
# contractions on Row. Everything pays in the quotient including all translates,
 i.e. defining/testing (93).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick
open Gap Cauchy Row Complex Finset Solution Braid
open scoped BigOperators
variable {α β η : Type*}
lemma oppos (b : Bool) (i : Axis) (p) : opp (foot b i p)=foot (!b) i (opp p) := by
  have he:= Gap.recur i p
  cases b <;> simp [foot,he]
lemma oppos_mi (b : Bool) (i : MI) (p) : opp (mi b i p)=mi (!b) i (opp p) := by
  have he (i : Axis) (m : ℕ) (p) : opp ((foot b i ^ m) p)=(foot (!b) i ^m) (opp p) := by
    induction m with
    | zero => simp
    | succ m t => rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,oppos,t]
  simp_rw [mi,Module.End.mul_apply,he]

abbrev Bil (α β : Type*) := J α →ₗ[ℂ] J β →ₗ[ℂ] SmoothGap

def directed (d : Bool) : Bil FIndex FIndex := jet fun i => mi false i.2 ∘ₗ book true (thread d i.1)
def colored : Bil GIndex GIndex := jet fun i => let m:=truck i.1 i.2.val.1; mi false i.2.val.2 ∘ₗ game true (curl m.1 m.2)

lemma revD (d : Bool) (a b : CJet) : directed d a b = -opp (directed (!d) b a) := by
  have h: directed d= (directed (!d)).flip.compr₂ (-opp) := equalsB (fun x y=>by
    change directed d (ket x) (ket y)= -opp (directed _ (ket y) (ket x))
    simp_rw [directed, on_ket, LinearMap.comp_apply,book,on_ket,oppos_mi]
    rw [← map_neg,← map_neg,flip_braid,recruit]; simp)
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b
lemma revG (x y : GJet) : colored x y = opp (colored y x) := by
  have h : colored=colored.flip.compr₂ opp := equalsB (fun i j=>by
    change colored _ _=opp (colored _ _)
    simp_rw [colored, on_ket]
    simp_rw [LinearMap.comp_apply,game,on_ket,oppos_mi,reads]
    rw [recruit,Bool.not_false,Bool.not_true] -- adjust
    rw [show ∀ i j k m,opp (curl k m i j)=curl i j k m from fun i j k m=>individuated (fun z p=>swirl _ _ _ _ p)])
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

@[simp] lemma psD (d : Bool) (a m b n) : directed d (C a m) (C b n)=mi false m (mi true n (thread d a b)) := by rw [directed,C,on_ket,LinearMap.comp_apply,desk]
lemma gradDR (d) (a b : CJet) (i) : directed d a (Cder (!d) i b)=Gap.step i (directed d a b) := by
  have h : (directed d).flip (Cder (!d) i b) = Gap.step i ∘ₗ (directed d).flip b := ket_ext (fun u=>by
    change directed d _ _ = Gap.step i (directed d (ket u) _)
    simp_rw [directed,on_ket,LinearMap.comp_apply,drive (fun c=> Wick.second d u.1 c)]
    exact (legs true false i u.2 _).symm)
  exact LinearMap.congr_fun h a
lemma gradDL (d) (a b) (i) : directed d (Cder d i a) b= -Gap.step i (directed d a b) := by
  rw [revD d _ b, revD d a b]; cases d <;>
    simp only [Bool.not_false, Bool.not_true]
  · change -opp (directed true b (Cder (!true) i a))= _; rw [gradDR,map_neg,neg_neg,Gap.recur]
  change -opp (directed false b (Cder (!false) i a))= _; rw [gradDR,map_neg,neg_neg,Gap.recur]
lemma fromK (v : GIndex) (i j : Axis) (n) : colored (ket v) (F i j n)=
    let u:=truck v.1 v.2.val.1; mi false v.2.val.2 (mi true n (curl u.1 u.2 i j)) := by
  rw [colored,on_ket]; dsimp only; rw [LinearMap.comp_apply,(curlRight _ _).cards]
lemma unroll (k m i j : Axis) (l h) : colored (F k m l) (F i j h)=
    mi false l (mi true h (curl k m i j)) := by
  have H : colored.flip (F i j h)=mi true h ∘ₗ game false (fun k m=>curl k m i j) := ket_ext (fun v=>by
    change colored _ _ = _; rw [fromK]; dsimp only
    rw [recruit,LinearMap.comp_apply,game,on_ket]; rfl)
  change colored.flip _ _=_; rw [H,LinearMap.comp_apply,(curlLeft _ _).cards, recruit]
lemma gradGR (a b : GJet) (i) : colored a (Gder i b) = Gap.step i (colored a b) := by
  have h: colored.flip (Gder i b)= Gap.step i ∘ₗ colored.flip b := ket_ext (fun v=>by
    change colored _ _ = Gap.step i (colored _ _)
    simp_rw [colored, on_ket]; rw [LinearMap.comp_apply, LinearMap.comp_apply,(curlRight _ _).moves]
    exact (legs true false i _ _).symm)
  exact LinearMap.congr_fun h a
lemma gradGL (a b) (i) : colored (Gder i a) b= -Gap.step i (colored a b) := by
  rw [revG (Gder i a),revG a b,gradGR,Gap.recur,neg_neg]
end YM.GaugeFieldConstruction.Wick

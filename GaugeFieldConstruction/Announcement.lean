import GaugeFieldConstruction.Replace

/-!
# Bundle contour. The one-place triples
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Conj Row Phys Function MeasureTheory Complex Set Wick U1 Lamp
open scoped Topology BigOperators ContDiff
variable {x y : E4} {χ : E4→ℝ} {B : Dollars}

def Eligible (χ : E4→ℝ) : Submodule ℂ Jobs where
  carrier:={f|∀ i z,z∈ Shore χ → ContinuousAt (f i) z}
  add_mem' a b:=fun i z h=> ContinuousAt.add (a i z h) (b i z h)
  zero_mem':=fun i z _=> continuousAt_const
  smul_mem' r a h:=fun i z p=> (continuousAt_const (y:=r)).smul (h i z p)
lemma comprised (i : E4) (A : Course B) (X : Forms) (p : ∀ a b z,z∈ Shore χ→ContDiffAt ℝ ∞ (X a b) z) : currentZ B X∈ Eligible χ := fun a z h=> (daily A X fun b=> p a b z h).continuousAt
lemma cr_plus (X Y: Forms) :currentZ B (X+Y)=currentZ B X+currentZ B Y := by ext1 i; ext1 j; simp [currentZ,Finset.sum_add_distrib,smul_add]
lemma cr_s (a : Forms) (r : ℂ) : currentZ B (r • a)=r • currentZ B a := by
  ext1 i; ext1 j; simp only [currentZ,Pi.smul_apply, Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=>smul_comm ..
lemma duo_eligible {α : Type*} (A : Course B) (Z:Axis→Axis→J α) (R : Wick.Bil α α) (v i) (p: i ∉ Shore χ): currentZ B (Duo Z R i v)∈Eligible χ := fun a z u=> (looks Z R A v (show z ≠ i from fun e=> p (e ▸ u)) a).continuousAt
lemma crest {V W : Forms} (p : currentZ B V∈Eligible χ) (b : Chassis x y χ) (q : currentZ B W∈Eligible χ) : Shell χ B (V+W)=Shell χ B V+Shell χ B W := by rw [Shell,cr_plus,pulse b p q]; rfl
lemma ace (F : Forms) (r : ℂ) : Shell χ B (r • F)=r*Shell χ B F := by rw [Shell, cr_s,atlas]; rfl

/- K L local responses on (97) tensor at x. -/
variable (m : ℂ) (V : Bool→ℂ) (a b : Book) {c : Chassis x y χ} 

def chevron (a : ℂ) (b : Bool→ℂ) (x y : E4) (v q : Book): Forms:= fun i j z=> tri z x y (plain i j a b) v q

lemma two_out (h : Cadre B x) (c : Chassis x y χ) :
    let M:=gStress m; let F:= fStress V
    Shell χ B (chevron m V x y a b)=((gloG M).glow χ B x y a.2.1 b.2.1+
        (gloF F).glow χ B x y a.2.2.1 b.2.2.1)+ (gloX F M).glow χ B x y a.2.2.2 b.2.2.2 := by
  intro M F; let g :=(gloG M).toll x y a.2.1 b.2.1; let f :=(gloF F).toll x y a.2.2.1 b.2.2.1; let t:= (gloX F M).toll x y a.2.2.2 b.2.2.2
  let X : Forms:= Duo M gaugeGap x a.2.1; let Y :Forms:= Duo M gaugeGap y b.2.1
  let P:= Duo F fGap x a.2.2.1; let Q:= Duo F fGap y b.2.2.1
  have ZZ : chevron m V x y a b = (b.1 • (X+P)+a.1 • (Y+Q))+ (g+f+t) := by
    ext1 i; ext1 j; ext1 z; rw [chevron, tri,pin₁,pinG,pinF]; simp only [zero_mul,zero_add,Pi.add_apply,Pi.smul_apply]; change _ + go z x y (M i j) _ _ + fo z x y (F i j) _ _ + (xu z x y (F i j)+ xd z x y (M i j)) _ _= _; rw [connect_g M,connect_f F,connect_x F M]
    simp only [toll,g,f,t,Duo,X,P,Y,Q,smul_eq_mul,M,F]; abel
  have px : x∉Shore χ:= fun H=> (c.gate H).1 rfl
  have py : y∉Shore χ:= fun H=>(c.gate H).2 rfl
  have G₁ : currentZ B g∈Eligible χ:= (gloG M).steady h.toCourse c _ _
  have G₂ :currentZ B f∈Eligible χ:= (gloF F).steady h.toCourse c _ _
  have G₃ :currentZ B t∈Eligible χ:= (gloX F M).steady h.toCourse c _ _
  have B₁:= duo_eligible h.toCourse M gaugeGap a.2.1 x px
  have B₂:= duo_eligible h.toCourse M gaugeGap b.2.1 y py
  have E₁:=duo_eligible h.toCourse F fGap a.2.2.1 x px
  have E₂:=duo_eligible h.toCourse F fGap b.2.2.1 y py
  have gp : ∀ j,∑ i:Axis, Phys.eyes i (M i j)=0 := fun i=> (div_tee m V i).1; have fp : ∀ j,∑ i:Axis,bones i (F i j)=0:= fun i=>(div_tee m V i).2
  have gl i a b:= Wick.g_L a b i; have fl i a b:= Wick.f_L a b i
  have p₂ : Shell χ B Y=0:= easy M gaugeGap (g_sym m) gp gl c h.toCourse _
  have q₂ : Shell χ B Q=0:= easy F fGap (f_sym V) fp fl c h.toCourse _
  have p₁ : Shell χ B X=0:= silence_aux M gaugeGap (g_sym m) gp gl (fun X : GaugePair=>8+weightG X.1.1+weightG X.2.1) (by intro i; omega) (fun i j k=> big_gG i j k m) c h _
  have q₁ : Shell χ B P=0 := silence_aux F fGap (f_sym V) fp fl (fun X : Spair=> 7+weight X.1.1+weight X.2.1) (fun i=>by omega) (fun X i j=>big_f V i j 0 X) c h _
  have he : currentZ B (X+P)∈Eligible χ:= cr_plus X P ▸ (Eligible χ).add_mem B₁ E₁ -- may mismatch
  have hw : currentZ B (Y+Q)∈Eligible χ:=cr_plus Y Q ▸ (Eligible χ).add_mem B₂ E₂
  have ht :currentZ B (g+f)∈Eligible χ:=by rw [cr_plus]; exact Submodule.add_mem _ G₁ G₂
  have hu :currentZ B (b.1 • (X+P) + a.1 • (Y+Q))∈Eligible χ:= by rw [cr_plus,cr_s,cr_s]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ he) (Submodule.smul_mem _ _ hw)
  rw [ZZ, crest hu c (show currentZ B (g+f+t)∈Eligible χ by rw [cr_plus]; exact Submodule.add_mem _ ht G₃),crest ht c G₃,crest G₁ c G₂]
  rw [crest (W:=a.1 • (Y+Q)) (by rw [cr_s]; exact Submodule.smul_mem _ _ he) c (by rw [cr_s]; exact Submodule.smul_mem _ _ hw), ace,ace]
  rw [crest B₁ c E₁, crest B₂ c E₂] -- X local defs
  rw [p₁,q₁,p₂,q₂,add_zero,mul_zero,mul_zero,zero_add,zero_add]; rfl

-- combined action on Book response: only ask receivability with one other.
def Earn (χ : E4→ℝ) (K : Dollars) (x y :E4) (a Z:Book) := ∀ b : Book, Shell χ K (chevron m V x y a b)=eye (y-x) (Wick.pair Z b)
lemma produced (h : Cadre B x) (c : Chassis x y χ) (z : Book) (hp:z.1=0) (u : (gloG (gStress m)).Latch χ B x y a.2.1 z.2.1)
    (v : (gloF (fStress V)).Latch χ B x y a.2.2.1 z.2.2.1) (w : (gloX (fStress V) (gStress m)).Latch χ B x y a.2.2.2 z.2.2.2) :
    Earn m V χ B x y a z := by
  intro b; rw [two_out m V a b h c]; rw [u,v,w]
  change _ = eye _ (cyc z b); rw [cyc,hp,zero_mul,zero_smul,zero_add,map_add,map_add, shineG]; rfl
end YM.GaugeFieldConstruction.Flux.One

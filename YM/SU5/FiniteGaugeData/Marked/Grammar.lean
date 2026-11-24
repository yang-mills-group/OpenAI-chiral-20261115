import YM.CF.Buffered.Form

/-!
# Atoms for `TestFamily true`
Coefficients retain their entire Borel system; we simply collect finite
CAR words on the fixed signed `basisC` frames (no bra-level changes needed
since the grammar has the allowed chiral orders already).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Sound
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
attribute [local instance] opCStarAlgebra

variable (K:Calibration) {S:Finset Cover} {b c:Bool}

abbrev Blot:= Cover × SpinIdx × SU.Slot
abbrev Chorus:= List Blot
variable {w : Bool} (u:Chorus)

def chord (a:Blot) : Family K := if a.2.1∈ plusHalf then creation K a.1 a.2.1 a.2.2 else removal K a.1 a.2.1 a.2.2
def sing := (u.map (chord K)).prod
def staves (S:Finset Cover):Prop:= ∀ x:Blot,x∈u → nodeC x.1∈S
def treble : Chorus→ Bool | [] => false | _ :: l=>true.xor (treble l)
lemma sing_append (a:Chorus):sing K (u++a)=sing K u*sing K a:=by rw [sing,List.map_append,List.prod_append]; rfl
lemma treble_append (a:Chorus):treble (u++a)=(treble u).xor (treble a):= by induction u with | nil => exact (Bool.false_xor _).symm | cons x u ih=> rw [List.cons_append,treble,ih,treble,Bool.xor_assoc]
lemma staves_append {a:Chorus}(p:staves u S)(h:staves a S):staves (u++a) S:=fun x v=> (List.mem_append.mp v).elim (p x) (h x)
lemma staves_one (x:Blot)(S:Finset Cover)(v:nodeC x.1∈ S): staves [x] S:=fun i p=> by rwa [List.mem_singleton.mp p]
lemma chord_t (x:Blot)(p:nodeC x.1∈ S): InTest K w S true (chord K x):=by
  unfold chord; split
  · next h=> exact .creator _ h p
  next h=> exact .remover _ h p
lemma sung (p:staves u S) : InTest K w S (treble u) (sing K u):=by
  induction u with
  | nil=> exact .one
  | cons x u ih=> exact .mul (chord_t K x (p _ List.mem_cons_self)) (ih (fun i h=> p _ (List.mem_cons_of_mem _ h)))
private lemma basis_size (m:Side)(x:Blot) : ‖basisC (K.c m) x.1 x.2.1 x.2.2‖ = 1 := by
  unfold basisC Lifted.winding; rw [norm_smul,Rush.fee_norm,one_mul]; simp [basisKet]
lemma moderate (m:Side)(v:Fields (K.c m))(x:Blot): ‖chord K x m v‖ ≤ 1 := by
  unfold chord; split
  · exact (Flare.cost_pe false _).trans_eq (basis_size K m x)
  exact (Flare.cost_pe true _).trans_eq (basis_size K m x)
lemma chorus_size (m:Side)(v:Fields (K.c m)): ‖sing K u m v‖ ≤ 1:=by
  induction u with
  | nil=> change ‖(1:FC (Single (K.c m)))‖ ≤ _; rw [norm_one]
  | cons x u ih=> exact (norm_mul_le (chord K x m v) (sing K u m v)).trans (mul_le_one₀ (moderate K m v x) (norm_nonneg _) ih)

def note (f:PairsC→ℂ)(u:Chorus): Family K := scalar K f * sing K u
lemma note_t {f:PairsC→ℂ} (h:Coeff w S f)(p:staves u S): InTest K w S (treble u) (note K f u):=by unfold note; simpa only [Bool.false_xor] using InTest.mul (.seed h) (sung K u p)
lemma note_v (f:PairsC→ℂ)(m:Side)(z:Fields (K.c m)): note K f u m z=f (Prod.map (onC _) (onC _) z) • sing K u m z := by
  unfold note scalar; simp only [Pi.mul_apply,Algebra.smul_mul_assoc,one_mul]; rfl
lemma note_plus (f g:PairsC→ℂ):note K (f+g) u=note K f u+note K g u:= by
  funext m z; simp only [Pi.add_apply,note_v,add_smul]
lemma note_times (f g:PairsC→ℂ)(a:Chorus):note K (f*g) (u++a)=note K f u*note K g a:= by
  funext m z; simp only [Pi.mul_apply,note_v,sing_append]; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul]
lemma pitched (f:PairsC→ℂ)(m:Side)(z:Fields (K.c m)): ‖note K f u m z‖ ≤ ‖f (Prod.map (onC _) (onC _) z)‖:= by
  rw [note_v,norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (chorus_size K u m z)

variable (S b)
def atoms: Set (Family K):={g| ∃ (f:PairsC→ℂ)(u:Chorus), Coeff true S f ∧ staves u S ∧ treble u=b ∧ g=note K f u}
def arias:=Submodule.span ℂ (atoms K S b)
variable {K S b}
lemma atom {f:PairsC→ℂ} {u:Chorus} (h:Coeff true S f)(p:staves u S)(x:treble u=b):note K f u∈arias K S b:= Submodule.subset_span (show _∈atoms K S b from ⟨f,u,h,p,x,rfl⟩)
lemma tone {f g:PairsC→ℂ}(h:Coeff true S f)(u:Coeff true S g): Coeff true S (f*g) := ⟨fun t=>by contradiction, env_mult h.env u.env,fun _ _ i j=> congrArg₂ (α:=ℂ) (β:=ℂ) (·*·) (h.locus _ _ i j) (u.locus _ _ i j)⟩
lemma ice : Coeff true S 1:=⟨fun p=>by contradiction, Girt.rite_c _,fun _ _ _ _=>rfl⟩
lemma pastel {f g:PairsC→ℂ}(h:Coeff true S f)(u:Coeff true S g): Coeff true S (f-g):= ⟨fun t=>by contradiction, Girt.kitE _ _ (· - ·) (by fun_prop) h.env u.env,fun _ _ i j=> congrArg₂ (α:=ℂ) (β:=ℂ) (·-·) (h.locus _ _ i j) (u.locus _ _ i j)⟩

lemma arias_mul {x y: Family K}(p:x∈ arias K S b)(v:y∈arias K S c): x*y∈arias K S (b.xor c) := by
  let T:= arias K S (b.xor c)
  change _∈ T
  refine Submodule.span_induction (s:=atoms K S b) (p:=fun x _=> x*y ∈ T) (fun X h=> ?_) (by rw [zero_mul]; exact T.zero_mem)
    (fun X Y _ _ h g=> by rw [add_mul]; exact T.add_mem h g)
    (fun X Y _ g=> by rw [Algebra.smul_mul_assoc]; exact T.smul_mem _ g) p
  refine Submodule.span_induction (s:=atoms K S c) (p:=fun y _=> X*y ∈ T) (fun Y t=> ?_) (by rw [mul_zero]; exact T.zero_mem)
    (fun A B _ _ h g=> by rw [mul_add]; exact T.add_mem h g)
    (fun A B _ g=> by rw [Algebra.mul_smul_comm]; exact T.smul_mem _ g) v
  obtain ⟨F,W,a,h,e,rfl⟩:=h; obtain ⟨G,Z,a',h',e',rfl⟩:=t
  rw [←note_times]; exact atom (tone a a') (staves_append W h h') (by rw [treble_append,e,e'])
lemma unitLink : scalar K 1 = 1:=by funext m z; change (1:ℂ) • (1:FC _)=1; simp
lemma whole {x:Family K}(h:InTest K true S b x):x∈arias K S b:=by
  have hs {f:PairsC→ℂ}(v:Coeff true S f) :scalar K f∈arias K S false:=by
    rw [show scalar K f=note K f [] from (mul_one _).symm]
    exact atom v (by simp [staves]) rfl
  have he (x:Blot)(h:nodeC x.1∈ S):chord K x∈arias K S true:=by
    have ht:=atom (K:=K) ice (staves_one x S h) (show treble [x]=true from rfl)
    simpa only [note,unitLink,sing,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul] using ht
  induction h with
  | seed v=>exact hs v
  | @creator x i b p v=> have h:= he (x,i,b) v; simpa [chord,p] using h
  | @remover x i b p v=> have h:= he (x,i,b) v; simpa [chord,p] using h
  | zero=> exact Submodule.zero_mem _
  | one=> rw [←unitLink]; exact hs ice
  | add _ _ p q=> exact Submodule.add_mem _ p q
  | smul a _ p=> exact Submodule.smul_mem _ a p
  | mul _ _ p q=> exact arias_mul p q

lemma test_span {f:Family K}(h:f∈arias K S b): InTest K true S b f := by
  refine Submodule.span_induction (p:=fun f _=>InTest K true S b f) (fun f p=>?_) (.zero) (fun _ _ _ _ a g=>.add a g) (fun i _ _ a=>.smul i a) h
  obtain ⟨g,x,h₀,u,rfl,rfl⟩:= p
  exact note_t K x h₀ u

lemma note_neg (f:PairsC→ℂ) (u:Chorus): (-1:ℂ) • note K f u = note K (-f) u := by
  funext m z; simp only [Pi.smul_apply,note_v,Pi.neg_apply,smul_smul,neg_one_mul]
lemma note_minus (f g:PairsC→ℂ) (u:Chorus):note K (f-g) u=note K f u+(-1:ℂ) • note K g u:= by
  rw [note_neg, ←note_plus,sub_eq_add_neg]
end YM.CF.Buffered.Afterglow.Sound

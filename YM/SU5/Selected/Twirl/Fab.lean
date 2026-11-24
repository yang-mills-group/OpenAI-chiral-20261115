import YM.SU5.Selected.Twirl.Sprite
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
-- assemble unnormalized spine first. `Coined` expects covector Leg with bound 1 => scale later.
-- allocate simultaneously: p old, p new higher by temporal shift h, remove masks and budget. C independent of D.
variable (n p h:ℕ)
local notation "B"=> p+h -- use in bodies not variable type
set_option pp.deepTerms true
def crestMap (f: Bool)(i: Fin p): Fin (p+h):=⟨i.val+(if f then h else 0), by cases f <;> simp only [ite_false,ite_true,Bool.false_eq_true]; all_goals omega⟩
variable {v:Type*}
lemma phase_ids (x:Fin p) (z:Coast)(t:Torch→ℂ)(k:SpinIdx) : rondo n B t z k (crestMap _ h true x) = prefixG (Ε (0:FaceL) (-(h:ℤ))) z * (rondo n B t z k (crestMap _ h false x)):=by
 unfold rondo nails forge; rw [← to_whole z, tintMono,prefix_zero]; simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]; by_cases p:k=2
 · subst k; simp only [if_true,one_mul, here_p,here_l]; rw [mul_left_comm _ (t _), ←fourier_add]; rw [show -(h:ℤ) + _ = -(strikeL n _ (crestMap _ h true x)) from ?_]; unfold strikeL crestMap; simp; ring
 simp [Ne.symm p]
variable {N:Side} (a:v→Site N×Fin p)
def perch (j:Bool) : v→ Site N× Fin (p+h):= fun i=> ((a i).1, crestMap p h j (a i).2)
def skyP (x:Bool×v):= perch p h a x.1 x.2
private lemma separate (u:p≤h)(i j:Fin p)(x y:Bool)(s:crestMap p h x i=crestMap p h y j): x=y∧ i=j:=by
 suffices x' : x=y by subst x; exact ⟨rfl,Fin.ext (Nat.add_right_cancel (Fin.mk.inj s))⟩
 have ht:=Fin.mk.inj s; cases x <;> cases y; exact rfl; simp only [Bool.false_eq_true,ite_false,ite_true] at ht; omega; simp only [Bool.false_eq_true,ite_false,ite_true] at ht; omega; exact rfl
lemma telescope_beacon {G D:Side}(t:p≤h)(u:Beacons G D p a) : Beacons G D (p+h) (skyP p h a):= by
 refine ⟨?_,u.spanX,u.spanT,fun i=> u.row _,fun i=> u.col _⟩; rintro ⟨i,x⟩ ⟨j,y⟩ g; obtain ⟨z,e⟩:=Prod.mk.inj g; obtain ⟨r,w⟩:=separate p h t _ _ _ _ e; exact Prod.ext r (u.mono (Prod.ext z w))
lemma TideFrame.weaker {G D:Side}{X Z: Coast→Wq p}{δ ε C C' δ' ε':ℝ}{w:ℕ} (v:TideFrame (G:=G) n p X Z D w δ ε C)(c:C≤C')(d:δ≤δ')(e:ε≤ε'): TideFrame (G:=G) n p X Z D w δ' ε' C':=
 ⟨v.late,v.early,v.ticket.mono (fun _ g N x _ _ u z=>by obtain ⟨b,j,k,l⟩:=g N u z; exact ⟨b.trans c,j.trans c,k.trans d,l.trans e⟩)⟩ -- syntax lambda implicit v type
section
variable {B':ℕ}(f:Fin p→Fin B')
def desc (X:Coast→ Wq B'): Coast→Wq p:= fun i=> Matrix.of fun x k=> X i x (f k)
variable [Fintype v][DecidableEq v]
lemma descent (X:Coast→ Wq B'): hire p (desc p f X) a=hire B' X (fun i=> ((a i).1,f (a i).2)):=by
 ext ⟨i,d⟩ l; unfold hire; rw [mask_mem,mask_mem, ←Prod.eta (p:=a l), freeze_charge,freeze_charge]; rfl
lemma hire_pay_s (X:Coast → Wq p)(d:ℂ): hire p (d • X) a=d • hire p X a:=by
 unfold hire; change freeze (d • (X∘brim N))*mask a= _; rw [freeze_smul,Matrix.smul_mul]
lemma freezePlus {K R:Type*} [Fintype K][DecidableEq K][Fintype R][DecidableEq R]{P:Side}(A B': Site P→ WRect K R) : freeze (A+B')=freeze A+freeze B':=by
 apply (sub_eq_iff_eq_add).1
 rw [←freeze_sub,add_sub_cancel_right]
lemma hire_pay_plus (A B':Coast→ Wq p) : hire p (A+B') a=hire p A a + hire p B' a:=by unfold hire; change freeze ((A∘brim N)+(B'∘brim N))*mask a= _; rw [freezePlus,Matrix.add_mul] -- silly
lemma hire_telescope (A: Coast → Wq (p+h)) (b:Bool) : hire p (desc p (crestMap p h b) A) a=hire (p+h) A (skyP p h a)* mask (Prod.mk b):= by
 rw [descent]; ext i j; unfold hire; rw [mask_mem,mask_mem,mask_mem]; rfl
end
private lemma orth_size {n m l:Type*}[Fintype n][DecidableEq n][Fintype m][DecidableEq m][Fintype l][DecidableEq l](L U:WRect n m)(Q:Op n)(P R: WRect m l)(h:Pᴴ*R=1)(u:‖P‖≤1)(q:‖R‖≤2){δ ε C:ℝ}(t:‖L‖≤ C)(l:‖U‖≤C)(x:‖Lᴴ*U-1‖≤δ)(v:‖Q*U‖≤ε) : ‖L*P‖≤ 2*C ∧ ‖U*R‖≤2*C ∧ ‖(L*P)ᴴ*(U*R)-1‖≤2*δ ∧ ‖Q*(U*R)‖≤2*ε:=by
 have e(A:WRect n m){q:ℝ}(p:‖A‖≤q): ‖A*R‖≤2*q:=by apply (Matrix.l2_opNorm_mul ..).trans; nlinarith only [show ‖R‖≤2 from ‹_›,p,norm_nonneg A] -- tune
 have k:0≤C:=(norm_nonneg U).trans l; refine ⟨(Matrix.l2_opNorm_mul ..).trans (((mul_le_of_le_one_right (norm_nonneg _) u)).trans (t.trans (by linarith))),e U l, ?_,(by rw [←Matrix.mul_assoc]; exact e _ v)⟩
 have hx:(L*P)ᴴ*(U*R)-1=Pᴴ*((Lᴴ*U-1)*R):=by rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,h,Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.mul_assoc Lᴴ U R]
 rw [hx]; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) ((Matrix.l2_opNorm_conjTranspose ..).trans_le u)).trans; apply (Matrix.l2_opNorm_mul ..).trans; nlinarith only [q,x,norm_nonneg (Lᴴ*U-1)]
section withJuniper
variable {G D: Side} {X Z:Coast→Wq (p+h)} {C δ ε:ℝ}{w:ℕ} (t:Frame (G:=G) n (p+h) X Z D w δ ε C) (u: p≤h)(o:p+h ≤ harbor n p)
local notation "X₀" A:max => desc p (crestMap p h false) A
local notation "Y₀" A:max => desc p (crestMap p h true) A
-- balance uses relative complex I. 
def manyX (b:Bool)(X:Coast→Wq (p+h)): Coast→ Wq p:= if b then I • Y₀ X else X₀ X
def lyricZ (Z:Coast → Wq (p+h)): Coast→ Wq p:= X₀ Z + I • Y₀ Z
include t u o
private lemma within_arc (c: Bool)(i:SpinIdx)(j:Fin p) : Color (lateR n p w i) (fun x=> desc p (crestMap p h c) X x i j) := Color_mono (t.late i _) (fun A v=>⟨v.1,v.2.1, by rw [v.2.2]; unfold depthL strikeL; have h:= (crestMap p h c j).isLt; omega⟩) -- unused A & u
private lemma within_ear (c: Bool)(i:SpinIdx)(j:Fin p) : Color (earlyR n p w i) (fun x=> desc p (crestMap p h c) Z x i j) := Color_mono (t.early i _) (fun A v=>⟨v.1, fun z=>by obtain ⟨a,e⟩:=v.2 z; rw [e]; unfold depthE strikeE; omega⟩)
omit o u t
abbrev leftS (b:Bool) (v:Type*) [DecidableEq v] : WRect (Bool × v) v:= if b then I • mask (Prod.mk b) else mask (Prod.mk b)
abbrev rightS (v:Type*) [DecidableEq v] : WRect (Bool × v) v:= mask (Prod.mk false)+ I • mask (Prod.mk true)
-- maybe mask `[Fintype]` requires due section variable included?
private lemma orthoS {v:Type*}[DecidableEq v][Fintype v](a b:Bool)(p:a≠b):(mask (Prod.mk a : v→ _))ᴴ* (mask (Prod.mk b: v → _))=0:=by ext; rw [mask_star_mem]; simp [mask,p]
private lemma boys (i:Bool) : Injective (Prod.mk i : v → _) := fun a b h=>(Prod.mk.inj h).2
private lemma leftS_norm (v:Type*) [Fintype v][DecidableEq v](i: Bool): ‖leftS i v‖≤ 1:= by
 cases i; exact mask_toll _ (boys _); rw [leftS,if_pos rfl,norm_smul,Complex.norm_I,one_mul]; exact mask_toll _ (boys _)
private lemma rightS_norm (v:Type*)[Fintype v][DecidableEq v]: ‖rightS v‖≤2:= by unfold rightS; apply (norm_add_le ..).trans; change _+ ‖leftS true v‖ ≤ _; linarith [leftS_norm v true,(mask_toll (Prod.mk false:v→_) (boys false))]
private lemma stepping (v:Type*)[Fintype v][DecidableEq v](i:Bool): (leftS i v)ᴴ * rightS v=1:= by
 cases i <;> rw [rightS, Matrix.mul_add,leftS];
 · simp only [Bool.false_eq_true,ite_false]; rw [mask_self _ (boys ..),Matrix.mul_smul,orthoS false true (by decide),smul_zero,add_zero]
 simp only [ite_true]; rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, orthoS true false (by decide),mask_self _ (boys ..), smul_zero,zero_add,smul_smul,show star I*I=1 by simp,one_smul]
variable [Fintype v][DecidableEq v]
lemma memory (X:Coast→Wq (p+h))(b:Bool): hire p (manyX p h b X) a = hire (p+h) X (skyP p h a)*leftS b v:= by
 cases b; exact hire_telescope ..; unfold manyX; simp only [ite_true]; rw [hire_pay_s,hire_telescope,leftS,if_pos rfl,Matrix.mul_smul]
lemma companion (Z:Coast→ Wq (p+h)): hire p (lyricZ p h Z) a=hire (p+h) Z (skyP p h a)*rightS v:=by
 unfold lyricZ rightS; rw [hire_pay_plus,hire_pay_s,Matrix.mul_add,Matrix.mul_smul,hire_telescope,hire_telescope]
include u o t
lemma takeT (b:Bool): TideFrame (G:=G) n p (manyX p h b X) (lyricZ p h Z) D w (2*δ) (2*ε) (2*C):= by
 refine ⟨fun i j=> ?_,fun i j=> (within_ear n p h t u o false i j).add ((within_ear n p h t u o true i j).smul I),t.ticket.mono ?_⟩
 · cases b; exact within_arc n p h t u o false i j; unfold manyX; simp only [if_true]; exact (within_arc n p h t u o true i j).smul I
 rintro M e N v _ _ a z; obtain ⟨h₁,h₂,h₃,h₄⟩:=e N _ (telescope_beacon p h a u z); have he:= rightS_norm v
 dsimp only; rw [memory,companion]; exact orth_size _ _ _ _ _ (stepping v b) (leftS_norm ..) he h₁ h₂ h₃ h₄
end withJuniper
-- buy both together. h advanced via grant. price clocks. earlier F shift relative to newer: give as screen type
structure Lift (p h:ℕ)(X Y: Coast→ Wq p): Prop where
 light (v:Coast): Y v = (I* prefixG (Ε (0:FaceL) (-(h:ℤ))) v) • X v
lemma lift_now (f:Torch→ℂ): Lift p h (manyX p h false (rondo n (p+h) f)) (manyX p h true (rondo n (p+h) f)):=by
 constructor; intro i; ext a b; change I * rondo n B f i a (crestMap p h true b) = I * _ * rondo n B f i a (crestMap p h false b); rw [phase_ids,mul_assoc]; -- proof may loop
lemma eros (G:Side)(g:8≤G.val)(u:p≤h)(e:n≥4)(o:p+h ≤ harbor n p) : ∃ C,1≤ (C:ℝ)∧∃ K:ℝ,0<K∧∀ (D:Side)(ε:ℝ),0<ε→ε≤1→∃ (w:ℕ)(X X' Z: Coast→ Wq p),Lift p h X X' ∧
    TideFrame (G:=G) n p X Z D w (K* Real.exp (-(1/2))^D.val+ε*(2*C)) (4*ε) C ∧ TideFrame (G:=G) n p X' Z D w (K* Real.exp (-(1/2))^D.val+ε*(2*C)) (4*ε) C :=by
 obtain ⟨C,c,K,k,v⟩:= starlight n (p+h) G g e; refine ⟨2*(C+1),by linarith,2*K,by linarith,fun D ε hp t=>?_⟩; obtain ⟨w,f,z,hK⟩:= v D ε hp t
 have he:2*(2*ε)≤4*ε:= by linarith
 have p' : 2*(K* Real.exp (-(1/2))^ D.val+ε*(2*C+1)) ≤ _:= show 2*(K* Real.exp (-(1/2))^ D.val+ε*(2*C+1)) ≤ 2*K* Real.exp (-(1/2))^D.val+ε*(2*(2*(C+1))) from (by linarith)
 exact ⟨w,_,_,_, lift_now n p h f,(takeT n p h hK u o false).weaker n p le_rfl p' he,(takeT n p h hK u o true).weaker n p le_rfl p' he⟩
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms phase_ids
#print axioms hire_telescope

#print axioms eros
#print axioms memory


import YM.CF.Tale.Leaf
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable{c f:Side}(M:Lattice.Ratio c f)
open StressFlux AnalyticBridge.VerifiedReset
variable (d':PlaqAxes)(o:Site c)(W:townX c)(s t:Step)
abbrev link_Y:= Exterior.linkSum W o (Lattice.oriented s t)
def curl_P := (4:ℝ)⁻¹ • (link_Y o W (posDir d'.1.1) (posDir d'.1.2)- link_Y o W (posDir d'.1.1) (negDir d'.1.2) - (link_Y o W (negDir d'.1.1) (posDir d'.1.2)-link_Y o W (negDir d'.1.1) (negDir d'.1.2)))
lemma born_k (Q:BudgetPoint): DifferentiableAt ℝ (fun W:townX c=> petals (increment 1 W) o d') 0:=by
 let F(U:Config SU.group c):= petals U o d'; have hp:= petals_bill (G:=SU.group) Q o d'; let k:=Q.order; have hh: ContDiffAt ℝ (∞) (F∘increment 1) 0 := (hp.smooth [] (by simp) 1).contDiffAt
 exact hh.differentiableAt (by decide)
lemma ring_l(Q:BudgetPoint): (fderiv ℝ (fun W:townX c=> petals (increment 1 W) o d') 0) W=curl_P d' o W :=by
 let F(s t :Step)(v:ℝ):= StressFlux.plate (line W v) o s t
 have h(s t:Step): HasDerivAt (F s t) (link_Y o W s t) 0:= Work.F03.curvature_of_hasDerivAt (Square.word_deriv o _ W)
 let x:=d'.val.1; let y:=d'.val.2
 let X(t):= petals (line W t) o d'
 have hp:HasDerivAt X (curl_P d' o W) 0:= (((h (posDir x) (posDir y)).sub (h (posDir x) (negDir y))).sub ((h (negDir x) (posDir y)).sub (h (negDir x) (negDir y)))).const_smul (4:ℝ)⁻¹
 exact (Push.side _ (born_k d' o Q) W).unique hp -- tune
private lemma around (p : Site f)(q:townX f)(a b:Step): link_Y p q a b=(flag a*flag b) • Exterior.linkSum q (atFace p a b) (square a.dir b.dir):=by
 rcases a with ⟨a,_|_⟩ <;> rcases b with ⟨b,_|_⟩ <;>
    simp [link_Y,Lattice.oriented,square, atFace, flag, posDir, negDir, Step.rev, Step.vec, Step.used, Exterior.linkSum, add_right_comm p, sub_eq_add_neg] <;> abel_nf
variable (Q:townX f) {A:ℝ}(P:group.Color)
lemma coil_X (u:Site f)(r:group.Color)(q:∀ i j:Step, i.dir=d'.1.1→ j.dir=d'.1.2→ ‖Exterior.linkSum Q (atFace u i j) (square d'.1.1 d'.1.2)-r‖≤ A) : ‖curl_P d' u Q-r‖≤ A :=by
 let G(i j:Step):=Exterior.linkSum Q (atFace u i j) (square i.dir j.dir); let W(i j: Step):= G i j - r; let x:=posDir d'.1.1; let y:=posDir d'.1.2; let X:=negDir d'.1.1; let Y:=negDir d'.1.2
 have h: ‖W x y + W x Y + (W X y + W X Y)‖≤4*A:= (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (q x y rfl rfl) (q x Y rfl rfl))) ((norm_add_le ..).trans (add_le_add (q X y rfl rfl) (q X Y rfl rfl)))).trans_eq (by ring))
 rw [show curl_P d' u Q-r=(4:ℝ)⁻¹ • (W x y+W x Y+(W X y+W X Y)) from ?_]; swap
 · unfold curl_P W G x y X Y; simp_rw [around]; dsimp only [flag,posDir,negDir]; simp; module
 rw [norm_smul]; refine (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq ?_; norm_num; ring
variable (k:ℝ)(j n:ℕ)(h:0<k)(p:4≤j)(v:4≤n)(T:Flight j n)(r m:ℕ)(w:f.val=c.val*T.L.val)
include h p v
-- take Vz defined as L maps
local notation "G"=> (deckY j n T w)
local notation "b"=> T.L
abbrev upper_F (Q:PlaqAxes)(X:group.Color)(O:Site c):= curt r O ((AnalyticBridge.VerifiedReset.wedge Q X).field O)
abbrev trade_u(x:townX c):townX f:= Heir.shaped (installed (deckY j n T w) (Lt k j n T)) x
lemma need_K : ∃ C a:ℝ,0<C∧0<a∧∀ (T:Flight j n)(M N:Side)(w:N.val=M.val*T.L.val)(o:Site M)(Q K:PlaqAxes)(D:group.Color) (r m:ℕ)(q:m ≤ r)(hk:2*m<M.val)(hL:5 ≤ T.L.val), let A:= trade_u k j n T w (upper_F r Q D o); ‖curl_P K ((deckY j n T w).embed o) A- ((T.L.val:ℝ)⁻¹)^2 • (if Q=K then D else 0)‖≤ C* ‖D‖ *((T.L.val:ℝ)⁻¹)^2*Real.exp (-a*m) :=by
 obtain ⟨a,C,ha,hC,Z⟩:=joint_T k j n h p v; refine ⟨2*C,a,by positivity,ha,fun T M N w o Q K D r m q hk hL=>?_ ⟩; intro F
 let U:=deckY j n T w; let P:=U.embed o; let z:=T.L; let d:=(z.val:ℝ)⁻¹; let Ξ:=(if Q=K then D else 0); let R:= d^2 • Ξ; let V:=upper_F r Q D o
 have he(x:Site N)(y): F (x,y)= MultiNext.SignedSource.Newt.load (installed U (Lt k j n T)) (Next.SectorChange.Flat.labels V) (x,Exterior.coord y):=Heir.roll_as V _ _
 have hx(X i): modeT z X Q.val.1 (Exterior.coord i) (Exterior.coord Q.val.2)= if X=Q.val.1 ∧ i=Q.val.2 then d^2 else 0:=by unfold modeT; simp_rw [show Exterior.coord i=Exterior.coord Q.val.2 ↔ i=Q.val.2 from Exterior.axisEquiv.injective.eq_iff]; rfl -- tune Dep rewrite
 refine coil_X K F P _ fun i j h g=>?_
 let x:= atFace P i j; let θ:= C/(T.L.val:ℝ)^2*(‖D‖*Real.exp (-a*m))
 let H s t:= F (x+step s,t)-F (x,t)
 have ht : U.parent x=o:= near_q _ _ 2 U o x (Square.near_face ..) (show _<T.L.val from by omega) -- dir of nearface
 have hp(s t):‖H s t- (if s= Q.val.1∧ t=Q.val.2 then d^2 else 0) • D‖≤ θ:=by
    unfold H; rw [he,he,←hx]; exact Z T M N w o x ht D Q r m q hk _ _ -- order
 rw [Square.cochain_square]; let y:=K.val.1; let p:=K.val.2; change ‖H y p-H p y - R‖ ≤ _
 have hv:‖H y p-R‖≤ θ:=by
    obtain ⟨⟨d1,d2⟩,v⟩:=Q -- ζ R depends tactic? issue
    apply le_trans _ (hp y p); unfold R Ξ; by_cases h: (⟨(d1,d2),v⟩:PlaqAxes)=K; · rw [if_pos h, if_pos (by rw [h]; exact ⟨rfl,rfl⟩)] -- tune
    rw [if_neg h, if_neg (fun g=> h (Subtype.ext (Prod.ext g.1.symm g.2.symm))), smul_zero,zero_smul]
 have he':‖H p y‖ ≤ θ:=by
    apply le_trans _ (hp p y); rw [if_neg ?_, zero_smul, sub_zero]; intro ⟨i,j⟩; have hg:y<p:=K.property; have hy:Q.val.1< Q.val.2:=Q.property; exact lt_asymm (i ▸ j ▸ hg) hy -- tune
 rw [sub_right_comm]; refine (norm_sub_le ..).trans ((add_le_add hv he').trans_eq ?_); unfold θ; rw [inv_pow]; ring
end YM.CF.Tale

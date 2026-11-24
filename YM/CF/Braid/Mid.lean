import YM.CF.Braid.Lath
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
-- general zero rel
lemma con_void (v:Axis→ℝ)(z:ℕ){F:CurRun (z+2)→Space (z+1)→ℂ}(h:0≤ A)(hp:∀ i,Pond M A (F i))(hv:∀ p:Corn (Keys (z+1)), fromCurl (cardR v (axes p)) (fun i=> F i (axes p))=0):
 let t:=z+1; let m:=Embedding.refl (Keys t); let J:=strands m; let K:=inlet F J
 Cycles (twist (axes v)) 2 K ∧ wall locus0 K ∧ Board (M+t) (A*topG 1^t) K:=by
 intro t m J K
 have he(p: Phase (Keys t)): Fin.tail (cardR v p)=J p:= by funext i; simp only [cardR,Fin.tail_cons]; rfl
 obtain ⟨hx,ht⟩:=turnZ (m:=cardR v) m he hv
 exact ⟨hx,ht,fun j x=>con_s m h (fun i=>F (Fin.cons j i)) (fun i=>hp _) _⟩
section ender
variable (v:Axis→ℝ){F: CurRun (t+2)→ Space (t+1)→ℂ}{V:SpanAt (t+1) 3}{R:ℕ}
-- package censorship
abbrev getSize (t R:ℕ):= rowDr t R
abbrev getRank(t M R:ℕ):= R+rankM (t+1) (M+getSize t R)
def getPay(t M R:ℕ)(A C:ℝ):= C*mate (t+1) R+(A+C*mate (t+1) R*topG 2)*rankK (t+1) (M+getSize t R)
lemma voices (ha:0≤ A)(hp:∀ i,Pond M A (F i))(he:0 ≤ C)(h:Board R C V)(hf:wall locus0 V)(hv:∀ p:Corn (Keys (t+1)),inlet F (strands (Embedding.refl _)) (axes p)=cob 2 (twist (axes v)) V (axes p)): wallS (cardR v) (getRank t M R) (t+2) (getPay t M R A C) F:=by
 let n:=t+1; let m:=Embedding.refl (Keys n); let U:= strands m
 have hu(p: Phase (Keys n)): Fin.tail (cardR v p)=U p:=by funext i; simp only [cardR,Fin.tail_cons]; rfl
 obtain ⟨X,hx,hX⟩:= transverse (m:=cardR v) m hu V he h (by exact hf) hv
 have hk:=mul_nonneg he (mate_pos n R); let J:=C*mate n R; let N:=M+getSize t R; let D:=A+J*topG 2
 have hD:0 ≤ D:= add_nonneg ha (mul_nonneg hk (by unfold topG; positivity)); have H:= too v hx hk
 apply wallS.cheaper (A:=max J (D*rankK n N)) _ (growsP X hx (fun j=>?_)) ?_ le_rfl
 · exact (max_le (le_add_of_nonneg_right (mul_nonneg hD (rank_p ..))) (le_add_of_nonneg_left hk))
 have ht:∀ a:CurRun n, Pond N D (fun p=> F (Fin.cons j a) p-stern (fun p=>cardR v p 0) X (Fin.cons j a) p):=by
    intro a; simp only [stern, Fin.cons_zero,Fin.tail_cons]; exact Pond.rest ((hp _).mono le_rfl (Nat.le_add_right ..)) ((H j a).mono le_rfl (Nat.le_add_left ..)) -- tune
 rw [show (fun p=>Fin.tail (cardR v p))=U from funext hu]; exact rails m _ hD ht (hX j)
lemma thicken (ha:0 ≤ A)(hp:∀ i,Pond M A (F i))(hv:∀ p:Corn (Keys (t+1)), fromCurl (cardR v (axes p)) (fun i=> F i (axes p))=0)(hC:0≤ C)(he:2+2*(t+1)>4∨∃ i:Axis,q (axes v) i≠0∧ ‖(q (axes v) i)⁻¹‖≤ C):
 let n:=t+1; let R:= paneR n 1 (M+n)
 wallS (cardR v) (getRank t M R) (n+1) (getPay t M R A (A*topG 1^n*palmJ C n 1 (M+n))) F:=by
 intro n R; obtain ⟨h₁,h₂,h₃⟩:= con_void v t ha hp hv
 have ht:0≤ A*topG 1^n:= by unfold topG; positivity
 obtain ⟨W,H,p,Hh⟩:=vacL v n 1 (M+n) hC he _ ht h₃ h₁ h₂; exact voices v ha hp (mul_nonneg ht (palm_pos C hC ..)) H p Hh
end ender
-- 2, homogeneous via press & lift same as Mimi, special V vanishing => K can
abbrev asked(M:ℕ):=peak 0 M+rowDr 0 (peak 0 (1+peak 0 M))
def payT2(M:ℕ):ℝ:=liftCost 0 M+(liftCost 0 M*topG 0*liftCost 0 (1+peak 0 M))*puff (peak 0 (1+peak 0 M))*topG 3
lemma staged{K:SpanAt 1 2}(h:0≤ A)(hk:Board M A K)(hv:JetWall 2 K)(he:Cycles missing 2 K)(hp:wall locus0 K): ∃ X:SpanAt 1 3,Board (asked M) (A*payT2 M) X∧ wall locus0 X∧∀ p:Corn (Keys 1),K (axes p)=cob 2 missing X (axes p):=by
 obtain ⟨X,HX,Hj,Hw,Ht⟩:= pure K h hk line_uniform (fun i j=> ((seal_tail i _).1 (hp i j)).1) he (Or.inl (by norm_num)) hv
 have hv:Cycles missing 3 (headPress X):= by
    intro p; rw [←press_cob]; funext a x; unfold headPress; rw [←Ht]; exact ((seal_tail p _).1 (hp p a)).2 x
 let T:Corn (Keys 1)→ Submodule ℂ (Run 0→ℂ):=fun p=>locus0 (clipVars p); have hU:Uniforms (Run 0) _ (stick 0) T:=var_uniform fun _ _ he=>by unfold T; rw [he]
 have hJ:JetWall 2 (headPress X):=press_jet Hj
 have he:0≤ A*liftCost 0 M:=mul_nonneg h (by unfold liftCost; positivity); have hz:0≤ A*liftCost 0 M*topG 0:=mul_nonneg he (by unfold topG; positivity)
 obtain ⟨Y,hY,yJ,Hy,Hs⟩:=pure (headPress X) hz (pressP HX he) hU (press_wall Hw) hv (Or.inl (by norm_num)) hJ
 let P:=liftCost 0 (1+peak 0 M); have hb:0 ≤A*liftCost 0 M*topG 0*P:=mul_nonneg hz (by unfold P liftCost; positivity)
 obtain ⟨D,hD,Hd,HD,hp'⟩:=press_pref Y hb hY yJ Hy (by
    intro p hr; have hh:p=0:=funext fun ⟨i,k⟩=> by rw [show i=0 from @Subsingleton.elim (Fin 1) _ _ _]; exact congr_fun hr k
    subst p; funext i x; exact (rays_at_zero ((hY i x).analytic.analytic_real _)).1 (yJ i x))
 let V:=X-cob 3 missing D
 refine ⟨V,?_,?_,fun p=> ?_⟩
 · have hB:= too (0:Axis→ℝ) hD (mul_nonneg hb (by positivity)); rw [twist0] at hB; apply Board.mono (Board.sub (Board.mono HX le_rfl (show _≤ asked M from Nat.le_add_right ..)) (Board.mono hB le_rfl (show _ ≤ asked M from Nat.le_add_left ..))) _ le_rfl
   exact le_of_eq (by unfold payT2 P puff; ring)
 · intro p a; apply (seal_tail p _).2; refine ⟨(lineTail p).sub_mem (Hw p a) (wall_cob missing HD p a),fun i=> ?_⟩; change headPress V (axes p) a i=0; unfold V; rw [press_sub,press_cob]; simp only [Pi.sub_apply]; apply sub_eq_zero.mpr; rw [Hs]; unfold cob; rw [hp']
 unfold V; rw [cob_sub,cob_zero,sub_zero,Ht]
lemma Jan {F: CurRun 2 → Space 1→ℂ}(h:∀ i,Rays 1 (F i ∘ axes)) : JetWall 2 (inlet F (strands (Embedding.refl (Keys 1)))):=by
 let m:= strand (0:Fin 1)
 have he(i:TypeFace 2)(j:Run 1): Rays (1+1) (fun p=> inlet F (strands (Embedding.refl (Keys 1))) (axes p) i j):= by
    let f(p:Space 1)(a:TypeFace 2)(b:Unit):= F (Fin.cons i (Fin.cons a default)) p
    have hh:JetWall 1 f:=fun a x=>h _
    have hx(p: Phase (Keys 1)): inlet F (strands (Embedding.refl (Keys 1))) p i j=cob 1 (projected m) f p (j 0) ():=by
       unfold inlet; rw [fromCurl_cons]; unfold cob Matrix.mulVec dotProduct; refine sum_congr rfl fun k _=>?_ ; unfold fromCurl; simp; rfl
    simp_rw [hx]; exact jets_cob (ray_symbol m) hh _ _
 exact he
lemma big2 {F:CurRun 2→ Space 1→ℂ}(hp:0 ≤ A)(hf:∀ i,Pond M A (F i))(h:∀ i,Rays 1 (F i∘axes))(hv:∀ p:Corn (Keys 1),fromCurl (cardR 0 (axes p)) (fun i=> F i (axes p))=0):
 let R:=asked (M+1); wallS (cardR 0) (getRank 0 M R) 2 (getPay 0 M R A (A * topG 1^1 * payT2 (M+1))) F:=by
 intro R; obtain ⟨he,ht,hx⟩:=con_void 0 0 hp hf hv; have hz:0 ≤ A*topG 1^1:=by unfold topG; positivity
 obtain ⟨X,HX,HQ,H⟩:=staged hz hx (Jan h) (twist0 ▸ he) ht; rw [← twist0] at H
 exact voices 0 hp hf (mul_nonneg hz (by unfold payT2 puff liftCost topG; positivity)) HX HQ H
end YM.CF.Braid

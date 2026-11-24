import YM.CF.Hive.Gets
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye
variable {N B m L:Side}{s:Sweep N}{X: Seal (Seat N)}
abbrev actS(s:Sweep N)(X:Seal (Seat N)):= X.map (boxA s).symm.toEmbedding
lemma actG_l(A:Sweep N)(X:Seal (Seat N)): actS A⁻¹ (actS A X)=X:=by ext; simp [actS,sitU] -- tune
lemma actG_s(s u:Sweep N)(X:Seal (Seat N)):actS (s*u) X= actS u (actS s X):=by
 ext; simp only [actS,mem_map_equiv,Equiv.symm_symm]; -- tune lemma
 rw [sitV ..]
def chip(S:Seal (Seat N))(A:Ids N): Sweep N:= (A (greet S (priorP A))).2.1
lemma chipA(S:Seal (Seat N))(p:S.Nonempty)(A: Ids N)(h: Injective (priorP A))(s:Sweep N):chip (actS s S) (bun s A)=s⁻¹*chip S A:=by
 let X:=actS s S; let z:=greet X (priorP (bun s A)); let u:=greet S (priorP A); let t:=boxA s; have he:=mastP S p (priorP A); have ht:= mastP X (map_nonempty.mpr p) (priorP (bun s A))
 have hv:t z=u:=by
    apply h; apply le_antisymm
    · have hp:= ht.2 (t.symm u) (mem_map_of_mem _ he.1); change priorP A (t z) ≤ priorP A (t (t.symm u)) at hp; rwa [Equiv.apply_symm_apply] at hp
    apply he.2; have hh:z∈X:=ht.1; simpa [X,actS] using hh
 change s⁻¹*(A (t z)).2.1= _; rw [hv]; rfl
variable {j:ℕ}{C a b d c v e H:ℝ}-- remove K
lemma grove_t(S:Seal (Seat N))(k:Sweep N)(p:Grove (terr _) S): Grove (terr _) (actS k S):=by
 have ht:= prow N (castX k⁻¹); -- inspect Exceed
 have hk:actS k S=roarD N (castX k⁻¹) S:=by rw [actS,map_eq_image]; exact congr_arg (fun f=> S.image f) rfl
 rw [hk]; exact ht.plus p
variable {V:Seal (Seat (CSide m B))}
def pullF (S: Seal (Seat (CSide m B)))(g:Seat (CSide m B)→ E)(x:Castle m B e S): Castle m B e S:=⟨fun i=>gauge g (x.val i),fun i=>(x.property.1 i).cov _,by exact tied (Sᶜ) _ _ _ _ x.property.2 (fun _ _=>rfl)⟩
def pullT(k:Sweep (CSide m B))(x:Castle m B e V):Castle m B e (actS k V):=⟨fun i=>flashA k (x.val i), fun i=>keepC (xtra _) _ _ _ (x.property.1 _),by dsimp; apply flashD k; apply agrees_mono x.property.2; intro i h; simpa [actS] using h ⟩
-- label normalized charges
abbrev warpC(X:Seal (Seat N))(A: Ids N): FC (Single N)→+*FC (Single N):= (teen (chip X A)).comp (Gaze (frameP A))
abbrev mallC(X:Seal (Seat N))(A: Ids N):FC (Single N)→+*FC (Single N):= (Gaze (frameP A)⁻¹).comp (teen (chip X A)⁻¹)
abbrev strideG(X: Seal (Seat (CSide m B)))(A: Ids (CSide m B)):= actS (chip X A) X
abbrev strideH(X: Seal (Seat (CSide m B)))(A: Ids (CSide m B))(x:Castle m B e X):Castle m B e (strideG X A):=pullT (chip X A) (pullF _ (frameP A) x)
lemma warped(X: Seal (Seat N))(A: Ids N)(V: FC (Single N))(h:Keys V): Keys (warpC X A V):=by rw [warpC,RingHom.comp_apply]; exact Keys.tour_b _ _ _ (Gaze (frameP A) V) (Keys.tour_b _ _ _ V h)
lemma mauled(X: Seal (Seat N))(A: Ids N)(V: FC (Single N))(h:Keys V): Keys (mallC X A V):=by rw [mallC,RingHom.comp_apply]; exact Keys.tour_b _ _ _ (teen (chip X A)⁻¹ V) (Keys.tour_b _ _ _ V h)
lemma gauge_one(U:FC (Single N)):Gaze 1 U=U:=by rw [Gaze,trade_p]; exact lot_one _
lemma morn(X:Seal (Seat N))(A: Ids N)(U:FC (Single N))(p:Keys U): warpC X A (mallC X A U)= U:=by
 simp only [warpC,mallC,RingHom.comp_apply]; let u:= chip X A; have hu: Keys (teen u⁻¹ U):=Keys.tour_b _ _ _ _ p; rw [gauge_t _ _ _ hu,mul_inv_cancel,gauge_one,yetL _ _ U p,inv_mul_cancel,lot_i U p]
lemma mare(X:Seal (Seat N))(A: Ids N)(U:FC (Single N))(p:Keys U): mallC X A (warpC X A U)=U:=by
 simp only [warpC,mallC,RingHom.comp_apply]; have hu: Keys (Gaze (frameP A) U):= Keys.tour_b _ _ _ _ p; rw [yetL _ _ _ hu,mul_inv_cancel,lot_i _ hu, gauge_t _ _ _ p,inv_mul_cancel,gauge_one]
lemma wore(s:Sweep N)(A:Ids N)(X: Seal (Seat N))(p:X.Nonempty)(h:Injective (priorP A))(U:FC (Single N))(q:Keys U):warpC (actS s X) (bun s A) (teen s U)= warpC X A U:=by simp only [warpC,RingHom.comp_apply,chipA X p A h]; have hh:frameP (bun s A)=(polarT s.charge ∘ frameP A) ∘ (castX s).anon N:= rfl; rw [hh,← yoT s _ _ q,yetL s _ _ (Keys.tour_b _ _ _ U q),mul_inv_cancel_left]
lemma chipT (f: Seat N→E)(A: Ids N)(S:Seal (Seat N)): chip S (threadG f A)=chip S A:=rfl
lemma worthZ (A:Ids N)(X: Seal (Seat N))(U: FC (Single N))(h:Keys U)(f:Seat N→ E): warpC X (threadG f A) (Gaze f U)= warpC X A U:=by simp only [warpC,RingHom.comp_apply,chipT]; rw [gauge_t _ _ U h,show frameP (threadG f A) * f=frameP A from ?_]; funext i; simp [frameP,threadG]
end YM.CF.Hive

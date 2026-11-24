import YM.CF.BProof.Gates.May

/- True field at assigned Mark neighborhood past Glow. expose Green irrespective flags read.
T from exact Angular.same...
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage.Setup
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R ν:ℝ}{S:Gates.Stage c w R ν}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
variable (T:PathData G)(θ:ℝ)(x:Pawn Y.yard)(h:T.Bounds c w R ν)(k:θ∈Set.Icc (1/2) 2)
variable {i:Y.yard.Index}(p:Space s) (j:TAxis)(X:Per s)(v:Along P Y T θ x)
-- warning v shadow rate label binder before h implicit might conflict
include h k v
private lemma horizontal_g (t:Y.yard.Gap i X)(u:Y.Green x (i,p)) : cd G (mag y (horiz X p j)) (area P Y T θ x (horiz X p j)) ≤ wc y+xi y :=by
 let D:=Y.yard; let a:=D.depth i X; have hx:= (Y.proceeds P T θ x v).2.2.2; by_cases l:a=0
 · apply le_trans (b:=xi y) _ (le_add_of_nonneg_left (coin_pos ..).le); have he:X=D.dEnd i:= (D.at_depth i X t).symm.trans (by rw [show D.depth i X=0 from l,atD_zero]); rw [he]; unfold dEnd; split; rename_i q; exact D.haven y Y.hall (area P Y T θ x) _ hx i q _ ((wet_h ..).2 (D.u_in i).le); rename_i q; exact D.haven y Y.hall (area P Y T θ x) _ hx (i+1) ((D.next i).mpr q) _ ((wet_h ..).2 (by simp))
 let b:Fin D.short:= ⟨a-1,by have hx:D.depth i X≤ D.short:=D.depth_le i X t; change a≤D.short at hx; omega⟩; have hb:b.val+1=D.depth i X:=by change a-1+1=a; omega
 let e:D.Door:= ((i,p),b,j); have he:horiz X p j=D.inter e:=by unfold inter e Angular.Yard.reach; dsimp only; rw [hb,D.at_depth i X t]
 rw [he]; refine le_trans (b:=wc y) ?_ (le_add_of_nonneg_right (coin_pos ..).le); rw [show area P Y T θ x (D.inter e)= Pawn.level x y T θ (soil P Y) (i,p) (b,j) from Pawn.paid_level Y.hall x y T θ (soil P Y) p (b,j)]; exact green_wave P Y T θ x h k _ u (i,p) ((Gauss.base _).start ..) (b,j)
private lemma horizontal_m (b: Bool)(u:Y.Green x (Y.yard.location i b,p))(t:Y.yard.Band i X)(q:flag (Y.yard.u i) X Y.yard.long=b)(e:angle Y.yard.long (along (Y.yard.u i) X)=if b then 1 else 0): cd G (mag y (horiz X p j)) (area P Y T θ x (horiz X p j)) ≤ wc y+xi y:=by
 let D:=Y.yard; let A:=area P Y T θ x; let X':=Y.proceeds P T θ x v; by_cases l:Y.yard.D i; exact (D.haven _ _ _ _ X'.2.2.2 i l _ ((wet_h ..).2 t)).trans (le_add_of_nonneg_left (coin_pos ..).le)
 let F:= obtainF P Y T θ x b (i:=i); have he: inlet (D.u i) D.long A b=F:=by apply D.sweeps_eq i A _ l; exact D.mix_field ..
 change _≤_; have H:= breezy P Y T θ x h k b p l u p (by simp) j; refine (cd_triangle G _ (inlet (D.u i) D.long A b (p,j)) _).trans (add_le_add ?_ (D.copy _ _ _ _ X'.2.2.2 X i t l b q e (p,j))); rw [he]; exact H
lemma tangent {r:ℕ}(t:Y.yard.Vic i r X)(u:4*r+4 ≤Y.yard.long)(p': Y.Green x (i,p)) : cd G (mag y (horiz X p j)) (area P Y T θ x (horiz X p j)) ≤ wc y+xi y := by
 rcases Y.yard.vic_split i r X (by omega) t with h₁|h₁|h₁
 · obtain ⟨he,q⟩:= Y.yard.cold_flag i X (by omega) h₁; exact horizontal_m P Y T θ x h k p j X v true p' h₁.2 he q
 · exact horizontal_g P Y T θ x h k p j X v h₁ p'
 obtain ⟨he,q⟩:=Y.yard.hot_flag (i+1) X (by omega) h₁; exact horizontal_m P Y T θ x h k p j X v false (by simpa [location]) h₁.2 he q
lemma pole {r:ℕ}(t:Y.yard.Vic i r X)(u:4*r+4 ≤Y.yard.long) : cd G (mag y (vert X p)) (area P Y T θ x (vert X p))≤ xi y :=by
 let X':=proceeds P Y T θ x v; have he:=Release.holds S.K S.P Y.yard T θ S.κ y (soil P Y) (room P Y) h k (Model.bought ..) x.sev x.gauss (area P Y T θ x) x.gap (Y.yard.mix_field ..) X'.2.1 X'.1 -- tune
 have hk:=(Y.yard.tone_vert _ X'.2.2.2 he i X p u t).aff; simpa only [Y.yard.roll_v, Gauge.mat_lieExp_zero,mul_one] using hk
lemma qualified {r:ℕ}(b:Bond s)(t:Y.yard.Vic i r (BProof.time b.1))(u:4*r+4≤Y.yard.long)(p': Y.Green x (i,BProof.space b.1)):
 cd G (mag y b) (area P Y T θ x b) ≤ wc y+xi y:=by
 rcases whichBond b with ⟨x,p,rfl⟩|⟨x,p,j,rfl⟩; exact (pole P Y T θ _ h k p x v t u).trans (le_add_of_nonneg_left (coin_pos ..).le); refine tangent P Y T θ _ h k p j x v t u ?_; rw [horiz,space_join] at p'; exact p'
end YM.CF.BProof.Gates.Stage.Setup

import YM.CF.Sour.Pose
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
lemma skyF {A:Type*}[LinearOrder A][Fintype A](F:FC A):∀ i:Finset A,Pastry.crumb (Sault.rind F) i=F i ∅:=fun i=>by rw [col,tileL,basis_act] -- tune vacuum
variable {F:Copy n}
namespace Crate
variable (h:Crate P X D Y V)
local notation "K"=> coll_T P X D V
local notation "Fy"=> Dwell n
local notation "M"=> Matrix (Finset (Dwell n)) (Finset (Dwell n)) ℂ
include h
def motion (h: Crate P X D Y V)(F:Copy n):Copy n:=fun x=> ⟨Sault.rind (coll_T P X D V x*(F x).val),light_e ((lift_v (h.lit x) (subset_univ _)).mul (life (fineShape (F x))))⟩
lemma salad(F:Copy n)(t:Measurable F): Measurable (h.motion F):=by
 have he:Measurable (fun x:Orbit n=> (h.motion F x).val):= ( (Pastry.cane (Dwell n)).eval.continuous_of_finiteDimensional.measurable).comp (h.virtue.mul (continuous_subtype_val.measurable.comp t)); change @Measurable _ (Cipher n) _ (borel _) _; have hp:@Measurable _ (Cipher n) _ Subtype.instMeasurableSpace (h.motion F):=he.subtype_mk; rw [@BorelSpace.measurable_eq (Cipher n) _ Subtype.instMeasurableSpace (Subtype.borelSpace _)] at hp; exact hp
lemma body_s (f:ThemeR X.val F)(p:Y.val ⊆ X.val): ThemeR X.val (h.motion F):=by
 refine ⟨fun i j x t=>?_, fun i=> ?_, h.salad _ f.keeps,fun i U=>?_⟩
 · apply Subtype.ext; change Sault.rind (K i*(F i).val) = _; rw [h.latch i j x t,f.same _ _ x t]; rfl
 · refine light_e ((lift_v (h.lit i) ?_).mul (life (f.lit i))); intro j t; exact mem_filter.mpr ⟨mem_univ _,p (mem_filter.mp t).2⟩
 let A:= sauce false false (tradew n U); let Z:Orbit n:=(Lattice.gauge U i.1,threadG U i.2)
 apply Subtype.ext; change Sault.rind (K Z* (F Z).val)= A (Sault.rind _); rw [show K Z=_ from h.tanG i U,show (F Z).val=A (F i).val from congrArg Subtype.val (f.gaugeX i U), show A (Sault.rind _) =_ from plower ..]; rw [show (sauce _ _ _) _ = _ from singm ..] -- tune rw occurrence
lemma lit0(x:Orbit n)(F:Copy n)(p:F x=0):(h.motion F) x=0:=Subtype.ext (show Sault.rind (K x * (F x).val)=0 from (by rw [p,Subalgebra.coe_zero,mul_zero,Sault.rind,map_zero]))
end Crate
namespace Marque
open Crate
variable {h C k μ:ℝ}{δ:ℕ}(H:Marque P X Y D V h C) (T:Fray P h δ X D F k)
local notation "U"=> H.toCrate
local notation "R"=> H.toCrate.motion F
include H T
lemma hosp : Lives P δ X D R:=fun i p=> T.loaf i (fun g=>p (H.toCrate.lit0 _ _ g))
omit H T
variable (w:3≤P.B){A:Firing n}{Z:Support (More n)}(x:Orbit n)(y:tangD n)
local notation "Θ"=> fun y:tangD n=> ((pressQ P Z x.1 y,x.2):Orbit n)
include w
lemma taskZ (q:D⊆ Z):D⊆ flags P.threshold (Θ y).1 ↔ D⊆flags P.threshold x.1:=by
 have ht: 12 ≤ 5*P.B:=by omega
 have hp:=flags_agree P.threshold x.1 (Θ y).1 D (agrees_mono (Taxi.wakeV _ q y) (Finset.coe_subset.mpr ((Yaw.touchK D).trans (Corona.halo_mono ht le_rfl))))
 exact ⟨fun l=> inter_eq_left.mp (hp.trans (inter_eq_left.mpr l)),fun l=>inter_eq_left.mp (hp.symm.trans (inter_eq_left.mpr l))⟩
include H T
lemma book (b:Y.val⊆X.val)(v:0 ≤ h)(p:0 ≤ C):Fray P h δ X D (H.toCrate.motion F) (C*k):=by
 obtain ⟨c,cv,cR,uK⟩:=H.vet; obtain ⟨B,hb,hs,hK⟩:=T.merit.pays; let A(i: Finset (Dwell n)):=∑ j: Finset (Dwell n), c i j*B j; have h0(i): 0≤ A i:=sum_nonneg fun j _=>mul_nonneg (cv ..) (hb j)
 refine ⟨⟨H.toCrate.body_s T.merit.toThemeR b,A,h0,fun x t Z s=>?_,?_⟩,H.hosp T⟩
 · let F'(y:tangD n): Orbit n:= (pressQ P Z x.1 y,x.2); refine ⟨Eventually.of_forall (fun i=> (fineShape _).allP),fun i=> ?_⟩; by_cases g:D⊆ flags P.threshold x.1; swap
   · have he(y:tangD n): R (F' y)=0:= H.toCrate.lit0 _ F (by by_contra f; exact g ((taskZ w x y s).mp (T.loaf (F' y) f).2))
     have hp:= Hake.Pence.const (k:=P.order) (0:tangD n) (0:ℂ); refine Pence.germ (show Pence P.order (fun _:tangD n=> (0:ℂ)) 0 (A i) from ⟨hp.smooth,hp.earned.trans ((norm_zero|>.le).trans (h0 i))⟩) ?_; filter_upwards with y; change _=Pastry.crumb (R (F' y)).val i; rw [he]; rfl
   let J(i j:Finset (Dwell n))(y:tangD n):ℂ:=V (F' y) i j*(F (F' y)).val j ∅; apply Pence.germ (g:=Hake.SongF (fun y=> (R (F' y)).val) i) (Pence.money (G:=J i) (fun (j:Finset _) (_:j∈univ)=> (uK x ⟨t,g⟩ _ s i j).twice ((hs x t s).haveP j))); filter_upwards [Vow.tick (Y:=Z) t] with y p; rw [Finset.sum_apply]; let u:=F' y; change _=Pastry.crumb (Sault.rind (coll_T _ _ _ _ _*(F u).val)) i; rw [H.toCrate.pointV (F' y) ⟨p,(taskZ w x y s).mpr g⟩, skyF, Matrix.mul_apply]
 unfold joinV; unfold A; simp_rw [mul_sum]; rw [sum_comm]; apply le_trans _ (mul_le_mul_of_nonneg_left hK p); unfold joinV; rw [mul_sum]; refine sum_le_sum ?_; intro i _; simp_rw [←mul_assoc,←sum_mul]; exact mul_le_mul_of_nonneg_right (cR i) (hb _)
end Marque
end YM.CF.Sour

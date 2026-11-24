import GaugeFieldConstruction.GrassFleetNX
import GaugeFieldConstruction.Toddy
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open Scree.Ing.Ivey.ShoreQ

variable (U:UNI (Single n))(q p:Bool)
variable (P:BudgetPoint)(R:Seat n≃Seat n)(a:Pane n→Pane n)
variable {v h x:ℝ}{S:Hubber n}{Q:Paper n}
abbrev MechanicalNX (S:Hubber n):Prop:= (∀ i j: Single n,U.val i j≠0→ R (aptK i)=aptK j)∧∀ (F:Lit n)(v:ℝ), MicroShipNX P S F v → MicroShipNX P (MustCap R S) (F ∘ a) v
lemma castHL_NX (r:Bool)(F:Lit n) (K:BudgetPoint)(W:Hubber n)(V:ℝ)(q:MicroShipNX K W F V): MicroShipNX K W (Ione.cast_B r∘F) V:=by
 let X:= Ione.cast_B r; have h:Micro K W ((Ione.cast_B r)∘F) V:=micro_e (micro_l _ (Ione.cap_X r) (show Micro K W F V from ⟨q.1,q.2.1,q.2.2.1,fun i _=>q.2.2.2 i⟩)) (one_mul _).le
 exact ⟨h.1,h.2.1,h.2.2.1,fun i=> ((q.2.2.2 i).linear X (Ione.cap_X r)).mono (one_mul _).le⟩
lemma tradeGXNX (t:MechanicalNX U P R a S)(V: Wa n→ℝ)(g:∀ i,MicroShipNX P S (Q i) (V i)∧(¬ DomainP S i→Q i=0))(i:Wa n): MicroShipNX P (MustCap R S) (CardCraft U q p a Q i) (Listing R p V i)∧(¬ DomainP (MustCap R S) i→ CardCraft U q p a Q i=0):=by
 let D:=MustCap R S; let L(j):Lit n:=(Q j)∘ a
 let Y (j):Lit n:= fun A=> boostX U p j i * cSignX (q.xor p) (L j A); have hv: CardCraft U q p a Q i=∑ j,Y j:=funext fun v=>by rw [Finset.sum_apply]; apply stripeQ
 have hx(j):MicroShipNX P D ((Ione.cast_B (q.xor p)) ∘ L j) (V j):= castHL_NX _ _ _ _ _ (t.2 _ _ (g j).1) 
 rw [hv]; constructor
 · apply MS_sumNX; intro j _; split
   · have hp:MicroShipNX P D (Y j) (‖boostX U p j i‖*V j):=by rw [show Y j=boostX U p j i • (Ione.cast_B (q.xor p) ∘ L j) from funext fun A=>by simp [Y,Ione.castT]]; exact MS_scaleNX _ (hx j) _
     exact MS_upNX _ hp (mul_le_of_le_one_left (g j|>.1.1) (boost_b ..))
   next z => rw [show Y j=0 from funext fun x=>by simpa only [Y,show boostX U p j i=0 from Classical.byContradiction fun k=> z (mem_filter.mpr ⟨mem_univ _,boost_D U p R t.1 j i k⟩), zero_mul,Pi.zero_apply]]; exact MS_zeroNX
 intro k; apply sum_eq_zero; intro j _; by_cases h: DomainP S j
 · have he: boostX U p j i=0:=Classical.byContradiction fun w=>k (show DomainP (MustCap R S) i from ?_)
   · funext x; simp [Y,he]
   have ht:=boost_D U p R t.1 j i w; cases i with
   | none=> trivial
   | some i=> cases j with
     | none=>exact ht.elim
     | some j=> rcases i with ⟨a,b,c⟩; rcases j with ⟨v,e,z⟩; exact ⟨mem_map_equiv.mpr (ht.2.1.symm ▸ h.1),mem_map_equiv.mpr (ht.2.2.symm ▸ h.2)⟩
 funext v; simp [Y,L,(g j).2 h,cSignX]
lemma massTransitNX (s:Sweep n): MechanicalNX (launchZ s) P (boxA s) (flashA s⁻¹) S:=by
 refine ⟨fun i j h=> Tye.birth_l i j (castX s) (spinU s.charge s.s) s.charge h, fun F v m=>?_⟩
 let M:= flashA s⁻¹; let K:= MustCap (boxA s) S; have he(i x:Pane n)(p:Lattice.Agrees K i x):Agrees S (M i) (M x):=by apply flashD _ i x; rw [sitU]; exact p
 refine ⟨m.1,Env.along m.2.1 (revM s⁻¹).measurable,fun i x p=> m.2.2.1 (M i) (M x) (he i x p),fun i=>?_⟩
 let t:= P.threshold; let L:= door_b s⁻¹ i
 have hv: Allows P.order (F∘ Shield.solo t (M i)) 0 v:=m.2.2.2 _; refine (comps L (x:=0) (map_zero L|>.symm ▸ hv) ?_).germ ?_
 · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i'; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro e; rw [show ‖L i' e‖=_ from cod_E s⁻¹ i i' e]; exact norm_le_pi_norm _ _
 refine Eventually.of_forall fun v=>congrArg F (show Shield.solo t (M i) (L v)=_ from ?_); unfold Shield.solo; rw [← map_smul]; exact (tour_p s⁻¹ i _).symm

lemma LatPasseNX (d:ℕ)(o:Seat n)(V:Sweep n)(F:Paper n)(u:DonauNX d P o h F v): DonauNX d P ((boxA V).symm o) h (Barber V F) (CaseL * v):=by
 obtain ⟨Z,g,q⟩:=u; let x:= (boxA V).symm o
 have hp:CanoeNX x d=MustCap (boxA V) (CanoeNX o d):=by unfold CanoeNX MustCap; change Lattice.halo d {x}=actY V (Lattice.halo d {o}); rw [←walkA]; unfold actY; rw [Finset.map_singleton]; rfl -- walkA orientation
 refine ⟨Listing (boxA V) (Typer V) Z,fun i=>?_ ,?_⟩
 · rw [hp]; exact tradeGXNX _ _ _ _ _ _ (massTransitNX P V) Z g _
 exact (wardPay (Typer V) (boxA V) Z (fun i=>(g i).1.1) h).trans (mul_le_mul_of_nonneg_left q (Nat.cast_nonneg _)) -- tune
#print axioms LatPasseNX
end MastTin
end YM.CF.XGarden
end

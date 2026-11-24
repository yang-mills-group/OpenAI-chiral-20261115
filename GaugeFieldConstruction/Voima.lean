import GaugeFieldConstruction.Parcht
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
variable {I:Type}[LinearOrder I][Fintype I]{N B:Side}{p:BudgetPoint}
variable (G:I→Oath.Zone (mid N B))(σ:I→ Seat (mid N B))(C:I→ I→ℂ)
open Py.Riant
variable (X:GramM (mid N B))(Yb W:Key I→ Vow.Pax (mid N B))(H:Ids (mid N B))(F:RegBudget (mid N B))(Kφ:Cusp (mid N B))
 (Ls Lt:ℝ)
variable (hq:∀ i x,River (fun z=> Yb z i x))(hy:∀ z∈hill I,Bake.Turf (Yb z))
 (hw:∀ i,Yb i=W i-W 0)
 (hc:∀ i U,Rue.FleetS X.p.threshold U.1 → Oath.Intent X.p (G i) U=coldE X.p (debit Yb i) U)
 (hk:∀ v:Orbit (mid N B),Rue.FleetS X.p.threshold v.1 → coldE X.p (W 0) v= owed_E (mid N B) (Ls+enerS_K X Lt v)+exponentL X.p F v.1+fuelV X.p Kφ v)
variable (u:Orbit (mid N B))(pU:Rue.FleetS X.p.threshold u.1)
include hq hy hw hc hk H pU
lemma Curtain (z:Key I): let T:=WritV σ (Bus1 (FacetE Yb (G_P G) H) σ C) z; let V:=WritV σ (BusQ σ C (fun z=>NQr z Kφ G)) z; let f:=Ls+enerS_K X Lt u; let s:= TurnArc σ C (α_ξ (G_s G)) z; coldE X.p (WritV σ (BusW σ C W) z) u = owed_E (mid N B) f + s • (1:Cipher (mid N B)) + exponentL X.p (F+ T) u.1 + fuelV X.p V u :=by
 intro T V f s; let S:=σ; let R:= TurnArc S C (E:=Cipher (mid N B))
 let A:= WritV σ (BusW σ C W); have hW(i y): River (fun z=>W z i y):=by
    have hf: (fun z=>W z i y)=fun z=> Yb z i y + W 0 i y:=funext fun x=>congrFun (congrFun (show W x=Yb x+W 0 from (by rw [hw,sub_add_cancel])) i) y
    rw [hf]; exact dub_V (hq i y) (zeroR _)
 obtain ⟨H₁,H'⟩:=BurnW S C W hW X.p u; let L:= α_ξ (G_s G); let K:= fun x:Key I=>NQr x Kφ G; let P:=FacetE Yb (G_P G) H
 have hL:River L:=by apply (tip_bank _ _ (fun i _=>?_)).1; have ht':(fun z:Key I=>z i*(G_s G) i)= fun z=> ((G_s G) i) • z i:=funext fun z=>mul_comm _ _; rw [ht']; exact River.scale (north_r _) _
 have hΦ(i D v): River (fun z=>K z i D v):= Qro ..
 let Z:= fun z=> coldE X.p (W z) u; let x':= fun z=>exponentL X.p (P z) u.1; let w':=fun z=>fuelV X.p (K z) u; let l':= hollow_L (N:=mid N B) ∘ L; let q':= owed_E (mid N B) f+exponentL X.p F u.1; let U':= fun z=> q'+l' z+x' z+w' z
 have heq : Set.EqOn Z U' (hill I):=by
    intro i g; change coldE _ (W i) _=_; rw [show W i=W 0+ Yb i from (by rw [hw]; abel),crep,hk u pU,presentations X.p Yb H G hy hc i g u pU]; unfold U' w' K NQr; rw [toast]; -- Arc.C.
    change _= q' + ((L i) • (1:Cipher (mid N B))) +x' i+(fuelV X.p Kφ u+fuelV X.p (Φstack (G_K G) i) u); unfold x' q' f P L; abel
 obtain ⟨hy,J⟩:= BurnX σ C P (growth_P Yb (G_P G) H hq) X.p u.1; obtain ⟨hz,Y⟩:=BurnQ σ C K hΦ X.p u
 have ht': R Z= fun z=> coldE X.p (A z) u:= H'
 let J':=dub_V (zeroR q') (sc_V hL hollow_L); have hg:R U'= ((fun _=>q') + hollow_L ∘ TurnArc σ C L) + R x'+ R w':=by
    unfold R S U'; rw [Arc_add _ _ (dub_V J' hy) hz,Arc_add _ _ J' hy,Arc_add _ _ (zeroR _) (sc_V hL _),Arc_const, Arc_map _ _ _ hL] -- ?.show
 exact ((congrFun ht' z).symm.trans ((congrFun (Arc_cong S C heq H₁) z).trans ((congrFun hg z).trans (by
    change q'+s • (1:Cipher (mid N B))+ R x' z+ R w' z= _; rw [show R x' z=exponentL X.p T u.1 from congrFun J z, show R w' z=fuelV X.p V u from congrFun Y z,ripe_H]; unfold q'; abel))))
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end

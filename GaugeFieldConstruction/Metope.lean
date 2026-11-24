import GaugeFieldConstruction.Kayf
import GaugeFieldConstruction.Cadent
import YM.CF.Salt.Grip
import YM.CF.Continuum.Winter
import YM.CF.Salt.Step
import YM.CF.Mica.Slide
import YM.CF.Cour.EdgeC
import YM.CF.Buffered.StepIdentity
import YM.CF.Urn.Role
/- Advance to arbitrary Sweeps and charge. Based on Winter.relative beta. X1 exact. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered
open Filter Function NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Reef
variable {m B N L : Side} {σ Cκ Λ' e v x y z η:ℝ} {j n:ℕ} {hj:Odd L.val} {Y:Pricing j L hj (Thread j)}
namespace Jubilee
open XGarden XGarden.MastTin XGarden.MastTin.ArtCart
lemma gearSector {Ω:Type}[LinearOrder Ω][Fintype Ω] {S:Finset Ω}{A:FC Ω}{b:Bool}(p:Fock.Sector S b A): Scion.Pitch Hake.bell Set.univ b.toNat A:=by
 induction p with
 | zero=> exact Scion.Pitch.null
 | one=> exact Scion.zeroW _
 | up i=> exact Scion.oneW (F:=Hake.bell) (i:=(true,i)) (Set.mem_univ _)
 | down i=> exact Scion.oneW (F:=Hake.bell) (i:=(false,i)) (Set.mem_univ _)
 | add _ _ h p=>exact h.add p
 | mul _ _ h p=>
    have he(v u:Bool): Nat.ModEq 2 (v.toNat+u.toNat) ((v^^u).toNat):=by cases v <;> cases u <;> decide
    exact (h.mu p).grade (he _ _)
 | scale _ q h=> exact h.stam q
lemma KeysSector {Ω:Type}[LinearOrder Ω][Fintype Ω] {S:Finset Ω}{A:FC Ω}(p:Fock.Sector S false A): Keys A:=Salt.tofu (gearSector p)
open Window Levier
lemma bandLot (i:Axis)(s:ℤ)(N:Side)(p:FC (Single N))(q:Keys p): let V:= Levier.ray (N:=N) false (plane i s); Urn.lotB false (Typer V) (launchZ V) p=theta (carR i s N) p:=by
 intro V; let L:=plane i s
 change Hive.teen V p=_; rw[show Hive.teen V p=Hive.yodel false L p from Hive.hono _ _ p q]
 have ht:= Hive.stag_s (b:=false) L (spinU false V.s) (pinLift i) p q (spinZ ..) (show JetS L.s false _ (pinLift i) from ?_)
 swap; · rw [show detX L.s=true from det_t i]; exact Scroll.mirrorX i
 refine ht.trans ?_; change Urn.lotB false (detX (Signed.mirror i)) _ p=_; rw [det_t]; rfl
lemma normLot (s:Sweep N) (A:FC (Single N)): ‖Urn.lotB s.charge (Typer s) (launchZ s) A‖=‖A‖:=by
 let b:=s.charge; let t:=Typer s; let U:=launchZ s
 change ‖Spire.tourP U b t A‖=_; generalize b=v;generalize t=a; cases v <;> cases a
 · exact singN ..
 · unfold Spire.tourP; simp only [if_true,theta,twist_norm,norm_cc]; rfl
 · exact singN ..
 unfold Spire.tourP; simp only [if_true,theta,twist_norm,norm_cc]; exact norm_cc _
structure SweepTurn (N:Side)(s:Sweep N)(A B:Mark N):Prop where
 ride :∀ V W, B (flashA s V, flashA s W)= Urn.lotB s.charge (Typer s) (launchZ s) (A (V,W))
variable {a b j k:Mark N}{σ:Sweep N}
lemma SweepTurn.add (p:SweepTurn N σ a b)(q:SweepTurn N σ j k):SweepTurn N σ (a+j) (b+k):=
 ⟨fun v w=> (congrArg₂ (·+·) (p.1 v w) (q.1 v w)).trans (map_add ..).symm⟩
lemma SweepTurn.mul (p:SweepTurn N σ a b)(q:SweepTurn N σ j k):SweepTurn N σ (a*j) (b*k):=
 ⟨fun v w=> (congrArg₂ (·*·) (p.1 v w) (q.1 v w)).trans (map_mul ..).symm⟩
lemma SweepTurn.unit : SweepTurn N σ 1 1:= ⟨fun _ _=>(map_one ..).symm⟩
lemma SweepTurn.smul (p:SweepTurn N σ a b)(z:ℂ):SweepTurn N σ (z • a) ((sign σ z) • b):= ⟨fun v w=> (congrArg (sign σ z • ·) (p.1 v w)).trans (Urn.visage ..).symm⟩
lemma pane_ray(i: Axis)(z:ℤ)(U: Pane N):flashA (Levier.ray (N:=N) false (plane i z)) U=Buffered.fling i z N U:= stir_e _ false U -- tune
lemma SweepTurn.refl {T:Support (More N)}(p:AtSupport false T a)(i:Axis)(z:ℤ): SweepTurn N (Levier.ray false (plane i z)) a (reflMark i z a) :=by
 let R:=Levier.ray (N:=N) false (plane i z); let K:= fling i z N
 refine ⟨fun v u=>?_⟩
 have hv: reflFields i z (flashA R v,flashA R u)=(v,u):=by rw [pane_ray,pane_ray]; exact Prod.ext (fling_invol i z v) (fling_invol i z u)
 unfold reflMark; rw [hv]; exact (bandLot i z N _ (KeysSector (p.allV _).sector)).symm
lemma SweepTurn.same (p:SweepTurn N σ a b)(q:SweepTurn N σ a k): b=k :=by
 funext i; obtain ⟨i,j⟩:=i; let v:= flashA σ⁻¹ i; let w:= flashA σ⁻¹ j; have he:i=flashA σ v:= (MastTin.goS σ _).symm; have hp:j=flashA σ w:=(MastTin.goS σ _).symm
 exact (congrArg b (congrArg₂ Prod.mk he hp)).trans (((p.1 v w).trans (q.1 v w).symm).trans (congrArg k (congrArg₂ Prod.mk he.symm hp.symm)))

open Afterglow
noncomputable def sailH (a:Shape)(b:Bool):ℂ→ₐ[ℝ]ℂ := if b.xor (detX a.s) then Complex.conjAe.toAlgHom else AlgHom.id ℝ _ -- tune
lemma sail_val (a:Shape)(b:Bool)(x:ℂ):sign (Levier.ray (N:=N) b a) x=sailH a b x:=by
 change cSignX (b.xor (detX a.s)) x=_; unfold sailH; cases (b.xor (detX a.s))<;>rfl
variable {K:Calibration}
def Festive (s:Shape)(q:Bool)(A B:Family K):Prop:=∀m:Side,SweepTurn (K.c m) (Levier.ray q s) (A m) (B m)
variable {F G T L:Family K}{s:Shape}{U:Bool}
lemma Festive.add (u:Festive s U F T)(v:Festive s U G L) : Festive s U (F+G) (T+L):=fun i=> (u i).add (v i)
lemma Festive.mul (u:Festive s U F T)(v:Festive s U G L): Festive s U (F*G) (T*L):=fun i=> (u i).mul (v i)
lemma Festive.unit : Festive (K:=K) s U 1 1:=fun _=> SweepTurn.unit
lemma Festive.same (p:Festive s U F T)(q:Festive s U F L):T=L:= funext fun i => (p i).same (q i)
lemma Festive.smul(p:Festive s U F T)(z:ℂ): Festive s U (z • F) (sailH s U z • T):=fun i=> (sail_val (N:=K.c i) s U z) ▸ (p i).smul z -- tune
lemma mirrorFest {S:Finset Cover}(h:InTest K true S false F)(a:Axis)(i:ℤ):Festive (plane a i) false F (Tower.mirror K a i F):= fun m=> SweepTurn.refl (h.support m) a i
#print axioms mirrorFest
end Jubilee
end YM.CF.Buffered
end

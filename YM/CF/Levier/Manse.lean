import YM.CF.Levier.Shaft
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
def toWish(s:Sweep N):=wish s.charge (castX s) G e
def toRoar(s:Sweep N):=roarD P (Shape.broad G (castX s))
def toSpin(s:Sweep N):=steer G s.charge (castX s)
lemma swept (j k:Sweep N)(x: Seal (Site (More P))): toRoar G j (toRoar G k x)=toRoar G (j*k) x:=by
 let a:=castX j; let c:= castX k; unfold toRoar; rw [keep_r, ←clan_b]; symm; let r:= j.charge; let b:=k.charge; have ht: j*k=ray (r.xor b) (joinX a c):=by rw [←ray_join,show ray (N:=N) r a= _ from ray_i j,show ray (N:=N) b c=_ from ray_i k]
 change _= roarD P (Shape.broad G (joinX a c)) x; -- rw occurrences j,k single
 rw [ht]; exact dartS ..
lemma shelf(j k:Sweep N)(x:cro G e): toWish G e k (toWish G e j x)=toWish G e (j*k) x:=by
 let a:=castX j; let c:=castX k; let r:=j.charge; let b:= k.charge; unfold toWish; rw [wish_seq]; change wish (r.xor b) (joinX a c) G e _= _; have ht: j*k=ray (r.xor b) (joinX a c):=by rw [←ray_join,show ray (N:=N) r a=_ from ray_i j,show ray (N:=N) b c=_ from ray_i k]
 rw [ht]; exact congr_fun (dartT ..).symm x
include h
lemma skim (j k:Sweep N)(X:Op (Iota G)): toSpin G k (toSpin G j X)=toSpin G (j*k) X:=by
 let a:=castX j; let c:=castX k; let r:=j.charge; let b:=k.charge; unfold toSpin; rw [steer_a _ _ _ h]; change steer G (r.xor b) (joinX a c) _=_
 have ht: j*k=ray (r.xor b) (joinX a c):=by rw [←ray_join,show ray (N:=N) r a= _ from ray_i j,show ray (N:=N) b c=_ from ray_i k]
 rw [ht]; let p:=joinX a c; exact cloud_x (r.xor b) G h X p.t (Lattice.lift (wrap N p.t)) p.s _ (wrap_lift _).symm
lemma skey (X:Op (Iota G)):toSpin G 1 X=X:=by
 have he:= skim G h 1 1 X; rw [one_mul] at he; refine (show Injective (toSpin G 1) from ?_) he
 exact (twist _).injective
omit h
lemma gish: ray (N:=N) false (incX 1)=1:=by change Sweep.mk _ (wrap N 0) _=Sweep.mk 1 0 false; rw [map_zero]; rfl
lemma sw_i (S: Seal (Site (More P))):toRoar G 1 S=S:=by
 unfold toRoar; rw [← show ray (N:=N) false (incX 1)=1 from ?_,dartS, show Shape.broad G (incX 1) =incX 1 by simp [Shape.broad,incX],reed]; exact gish -- gish h included
lemma want_i(x: cro G e): toWish G e 1 x=x:=by unfold toWish; rw [← show ray (N:=N) false (incX 1)=_ from gish]; rw [show (ray (N:=N) false (incX 1)).charge=false from rfl,dartT,wish_i]
variable {V:Set ℂ}
lemma siteB(X:ℂ→ Chin N)(u:IsOpen V)(p:DifferentiableOn ℂ X V):DifferentiableOn ℂ (fun z=> gateC false a (X z)) V:=by
 intro z g; apply DifferentiableAt.differentiableWithinAt; exact differentiableAt_pi.mpr fun i=>differentiableAt_pi.mpr fun j=> differentiableAt_pi.mp (differentiableAt_pi.mp (p.differentiableAt (u.mem_nhds g)) _) _
lemma duet_h(X:ℂ→Chin N)(u:IsOpen V)(p:DifferentiableOn ℂ X V): DifferentiableOn ℂ (fun z=>gateC true a (X (star z))) (star ⁻¹' V):=by
 intro z g; apply DifferentiableAt.differentiableWithinAt; apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
 let f(t:ℂ):= X t (elf a i) (j.xor (a.s.flip i.2)); have ht:DifferentiableAt ℂ f (star z):=differentiableAt_pi.mp (differentiableAt_pi.mp (p.differentiableAt (u.mem_nhds g)) _) _
 have he {m:Type}[DecidableEq m][Fintype m](A:ℂ→Op m)(k:DifferentiableAt ℂ A (star z)): DifferentiableAt ℂ (fun x=> cc (A (star x))) z:=by
    apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j; exact (differentiableAt_star_conj_iff.mpr (differentiableAt_pi.mp (differentiableAt_pi.mp k i) j))
 exact (he _ ht.fst).prodMk (he _ ht.snd)
lemma looks_p(F:cro G e→ℂ)(p:Looks _ F): Looks (cro G e) fun x=> cSignX b (F (wish b a G e x)):=by
 cases b; · intro V u γ v; exact p V u (wish false a G e ∘ γ) (((siteB (a.broad G) _ u v.fst.fst).prodMk (siteB a _ u v.fst.snd)).prodMk (siteB (a.broad G) _ u v.snd))
 exact realigns p (wish true a G e) fun V u γ v=> ((duet_h (a.broad G) _ u v.fst.fst).prodMk (duet_h a _ u v.fst.snd)).prodMk (duet_h (a.broad G) _ u v.snd)
end YM.CF.Levier

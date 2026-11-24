import WakeRoad.Mirror
/-! # Flat price gauge conservation for n mixed probes without identifying price
 with true gauge-sector expectation. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Classical
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
lemma alley_unchanged {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{U: UNI n}{x y:Wave n}{S:Finset n}{P:Op n}
    (q:Sea (cutM S) x)(p:IsStarProjection P)(v:Sea P y)
    (h:twist U (cutM S)=cutM S)(he:twist U P=P)(F:FC n): alleyR x y (twist (quantU U) F) = alleyR x y F :=by
 let R:=arum U false false x
 have ht:sings false U (cutM S)=swapX false (cutM S):=h
 have hy: Sea P (R y):=by
    constructor
    · nth_rw 1 [←tour_line U false false P P p he]; rw [show R y=arum U false false x y from rfl,←arum_act,v.1]
    exact (arum_norm U false false S q ht y).trans v.2
 have hl(w : Wave n): inner ℂ x (R w) = inner ℂ x w :=by nth_rw 1 [← arum_self U false false S q ht]; exact arum_globe U false false S q ht ..
 rw [alley_match p v hy]; change (inner ℂ x _)⁻¹ * inner ℂ x (acts (Spire.tourP U false false F) (arum U false false x y))=_
 rw [←arum_act,hl,hl]; rfl

variable {N:Side}{M:Jill.Male} {j:ℕ} (x:Wave (Single N))(p:IsStarProjection (spar j M (1:Pane N)))(v: Sea (spar j M (1:Pane N)) x)
namespace Hearth
local notation "ℰ"=>spar j M (1:Pane N)
include p v
lemma still_order (T:SU.E)(h: twist (tradew N (fun _=>T)) ℰ=ℰ)(f:FC (Single N)): alleyR (mateK N) x (twist (quantU (tradew N (fun _=>T))) f)= alleyR (mateK N) x f:= alley_unchanged (by rw [←touchP]; exact tickB N) p v (by rw [←touchP]; exact Cascade.tick_g _) h f
open Ballad
-- arbitrary palette of color currents
lemma stand_manifold {a:Type*}(L:List a)(W:a → Cover)(G:a→Twah.DirSpin)(A:a → ColorL)(r:ℕ)(T:SU.E)(h: twist (tradew N (fun _=>T)) ℰ=ℰ) :
    alleyR (mateK N) x ((L.map (fun i=> wrapCurrent (W i) (G i) r N (SU.group.adjoint T (A i)))).prod)=alleyR (mateK N) x ((L.map (fun i=> wrapCurrent (W i) (G i) r N (A i))).prod):= by
 let u(i):=wrapCurrent (W i) (G i) r N (A i); let g:= twist (quantU (tradew N (fun _=>T)))
 have he(i): wrapCurrent (W i) (G i) r N (SU.group.adjoint T (A i))=g (u i):=current_cov _ _ _ _ (1,1) (fun _=>T)
 simp_rw [he]
 have ht (L:List a): (L.map (fun i=>g (u i))).prod =g ((L.map u).prod):=by
    induction L with
    | nil=>
      let U:=quantU (tradew N (fun _=>T))
      change 1= twist U (1:Op (Finset (Single N)))
      rw [twist_formula,mul_one,U.property.2]
    | cons a l h=> simp only [List.map_cons,List.prod_cons]; rw [h,map_mul]
 rw [ht L]; exact still_order x p v T h _
#print axioms stand_manifold
end Hearth
end YM.CF.Hiro

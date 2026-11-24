import ZecaCredit
import YM.SU5.FiniteGaugeData.Poin.Loot
import YM.SU5.FiniteGaugeData.Poin.Celadon
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin Boundary Probe

structure Moment (H: Hilbert) where
 n:ℕ
 op:H.Op

namespace Moment

variable (D:Moment H)

abbrev field := σV S D.op D.n

abbrev cost (t u:ℝ≥0) :=
 parabola S D.n (duration t)* D.op * parabola S D.n (duration u)

def dagger := { D with op:=star D.op }

abbrev form (p:E4)(x y:Bench S):=
 lucent S (hall S D.n x) (hall S D.n y) D.op p

lemma wage : credit S (D.cost S) D.n D.op:=by
 intro t u g h
 unfold cost
 rw [←mul_assoc,←mul_assoc, show R^D.n * _=_ from K_E S D.n t g,mul_assoc _ _ (R^D.n)]
 exact (congrArg (S.E t * D.op * ·) (parabolaE S D.n u h)).symm

lemma coin_ext (U:Moment H)(h:D.n=U.n)
 (p:D.field S=U.field S):D=U:=by
 obtain ⟨n,A⟩:=D
 obtain ⟨m,B⟩:=U
 dsimp only at h; subst m; congr
 have dh:DenseRange (hall S n):=by
     refine Dense.mono ?_ (bench_warm S)
     intro x q; let y:Bench S:=⟨x,q⟩
     exact ⟨park S (Cache S n) (autumn S _ ((Commute.refl R).pow_left _)) y,
      congrArg Subtype.val (cache_park S y n)⟩

 -- assizes argument, DeSoto.encase
 refine DFunLike.coe_injective (dh.equalizer A.continuous B.continuous ?_)
 funext x; apply dh.eq_of_inner_right ℂ; intro y
 let f(z:E4):= lucent S (hall S n y) (hall S n x) A z-lucent S (hall S n y) (hall S n x) B z
 have h(V:H.Op):Continuous (lucent S (hall S n y) (hall S n x) V):=continuous_const.inner (village ..)
 have hf:f=(fun _=>0) := Canopy.oracle _ ((h A).sub (h B)) (fun g=>by
    unfold f
    simp_rw [mul_sub]
    rw [integral_sub (sell ..) (sell ..),← assizes,← assizes]
    rw [show ℑ S A g n=ℑ S B g n from DFunLike.congr_fun p g,sub_self])
 have hv:=congrFun hf 0
 unfold f lucent at hv; rw [vroot,vroot] at hv
 exact sub_eq_zero.mp hv
end Moment

/-- Statements of the real price at any charge. -/
structure RealStamp :Prop where
 solid : Dense (Bench S:Set H)
 moves : S.unit.Spectrum S.ℚmeasure
 time (x:H): (S.ℚmeasure.diagonal x).support ⊆ {p:E4|0≤p a}
 clock (T:OS.Semigroup H a)(e:M T=M S) : T=S
 unique (D V:Moment H): D.n=V.n → D.field S=V.field S → D=V
 cost (D:Moment H)(x y:H)(s t:ℝ≥0)(g:0<s)(h:0<t):
    inner ℂ x (D.cost S s t y) =
     D.form S 0 ⟨S.E s x,ray S x s g⟩ ⟨S.E t y,ray S y t h⟩
 adj (D:Moment H)(f:Test4)(x y: Bench S):
   inner ℂ (D.field S f x).val y.val=
       inner ℂ x.val (D.dagger.field S (bar f) y).val
 scalar (D:Moment H)(f:Test4)(x y:Bench S):
   inner ℂ x.val (D.field S f y).val = ∫ p, f p * D.form S p x y
 dist (D:Moment H)(x:Bench S):
   Continuous (fun f=>(D.field S f x).val)
 travel (D:Moment H)(p:E4)(f:Test4)(x:Bench S):
    usher S p (D.field S f x)= D.field S (ahead p f) (usher S p x)

lemma realStamp : RealStamp S:=by
 refine ⟨bench_warm S,S.joint,S.nonneg,fun T=> derive_full T S,fun D V=> D.coin_ext S V,
    ?_, fun _ _ _ _=> sees_κ ..,fun _ _ _ _=>assizes ..,fun _ _=>singular ..,fun _ _ _ _=> attends ..⟩
 intro D x y s t g h
 unfold Moment.form lucent; rw [vroot]
 exact rec_pair S _ _ (Moment.wage S D) g h x y
#print axioms realStamp

end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca

import YM.SU5.FiniteGaugeData.Maypole.Optic
import ZecaPavilion
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Celeritas Land Leal Breve Poin.Gem Boundary Probe Flute
open Vp.Folio
open Seld.Vp Seld.Vp.Luft _root_.YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)
   (Ω:Bench S)(hΩ:∀x:E4,M S x Ω.val=Ω.val)
   (p:Filled S G Ω.val)

include p hΩ
lemma climb_all : G.Climb S Ω=⊤:= by
 apply G.fullCanopy _ _ hΩ; constructor
 intro P _ _ s e c a h
 let L:= (1-P).ker
 have rflK (y): y∈L↔y=P y:= by change (1-P) y = 0 ↔ _;rw [_root_.sub_apply,sub_eq_zero];rfl
 have k(A:H.Op)(v: Commute A P): Keeps L A:=fun x q=> (rflK _).2
    ((congrArg A ((rflK x).1 q)).trans (DFunLike.congr_fun v.eq x))
 have z:=p L ⟨(1-P).isClosed_ker,(rflK _).2 a.symm,fun _=>k _ (e _),fun _=>k _ (c _),fun _=>k _ (h _)⟩
 ext1 x
 exact ((rflK x).mp (z ▸ Submodule.mem_top)).symm

lemma climb_money : Dense (Submodule.span ℂ (John S Ω.val G.dep G.grade) : Set H.space):=by
  let V := ArcJ S G Ω.val 0
  have a: V⊆ John S Ω.val G.dep G.grade:=by
    rintro x ⟨L,t,_,f⟩; exact ⟨L,t,f⟩

  apply Dense.mono (show (Submodule.span ℂ V:Set H.space)⊆ (Submodule.span ℂ (John S Ω.val G.dep G.grade):Set H.space) from
     Submodule.span_mono a)
  apply evergreen _ S G Ω.val p
  refine eventFern _ _ _ hΩ _ ?_ rfl
  intro x v
  obtain ⟨L,t,h,f⟩:=v
  exact grown _ _ ⟨L,t,h,f,fun _ _=>Or.inl rfl⟩

-- cf Luft.master
theorem petals (q:G.Tile S Ω): Cinema S:=by
  let hp (r:Mink.Ray):Shelf S (reduced (magnet r)):= budget S r
     (fun e=> sightseeing G S e Ω hΩ q (climb_money S G Ω hΩ p))
  have k:=climb_all S G Ω hΩ p
  obtain ⟨X,c⟩:=G.actionR S Ω hΩ (G.tilt_good S Ω q) hp k
  have hX:X.orbit=S.unit:=by
    apply (show ∀ X Y:Spectral.Orbit H E4,X.translation=Y.translation→ X=Y from fun X Y z=>by cases X; cases Y; congr); exact funext (G.subsidiary S Ω hΩ k X c)
  change S.ℚmeasure.region _=_
  rw [timeCone];change S.unit.P.region _=_;rw [←hX];apply X.south;unfold Action.μ;rw [hX];exact S.nonneg
#print axioms petals
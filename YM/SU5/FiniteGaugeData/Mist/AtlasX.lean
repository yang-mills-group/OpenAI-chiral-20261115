import YM.SU5.FiniteGaugeData.Mist.Utah
/-! ## Stationarity on partial projections -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
namespace Kodiak
variable {L:Side}{a:Axis}{H:Hilbert}(B:List Axis)(P:Terrace H L a)(z:1<L.val)(b:Axis)(p:b∈ B)
variable (x:CoreH (GroupR P B))(η:b≠ a)
include p z η
lemma planted : (∀ t:ℝ,mistU P B z t b p x=x) ↔ ∀ (s:ℕ)(i:ℤ)(p':Allows a b i), P.stepT s b i p' (cpo (GroupR P B) x)=cpo (GroupR P B) x:= by
 let K:=GroupR P B; have he(s:ℕ)(k:ℤ)(p':Allows a b k): P.stepT s b k p' (cpo K x)= cpo K (mistU P B z (spinT L s k) b p x):= Eq.trans (DFunLike.congr_fun (Cot.cpo_fun (pay_Group P b s k B p')) x) (congrArg (fun f:(CoreH K).Op=> cpo K (f x)) (streamU B P z s k b p η).symm) -- argument order
 constructor
 · intro h x k p'; rw [he, h]
 intro h t; refine congr_fun (vistas z (fun u=> mistU P B z u b p x) (fun _=>x) (unitC P B z p x).continuous continuous_const (fun r=>?_)) t; obtain ⟨s,k,rfl⟩:=(frequentT L r).exists; apply Subtype.ext; exact (he s k (fun i=> (η i).elim)).symm.trans (h s k _)
end Kodiak
end YM.CF.Buffered.Afterglow.Hierarchy.Mist

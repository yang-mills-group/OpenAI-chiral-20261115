import GaugeFieldConstruction.Argyll
import YM.CF.Roots.Sail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots
open Function Mew Set Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
namespace GJ
-- trim Group key monomial using Dune: choose i,j with σ i=σ j; absence trivial else permutation and derivative.Face.
variable {I E J:Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
def stalk(l:List I)(S:E)(z:Key I):E:=(l.map z).prod • S
lemma stalkR(l:List I)(S:E): River (stalk l S):=by
 induction l with
 | nil=> rw [show stalk ([]:List I) S=fun _=> S from funext fun z=>by simp [stalk]]; exact zeroR S
 | cons i l ih=>
    have he: stalk (i::l) S=pulseV (ContinuousLinearMap.lsmul ℂ ℂ) (fun z:Key I=> z i) (stalk l S):=funext fun z=>by simp [pulseV,stalk,mul_smul]; exact smul_comm .. -- tune CLM
    rw [he]; exact prodR _ (north_r _) ih
variable (σ:I→J)
lemma noStem (l s:List I)(p:¬ψS σ l)(t:ψS σ s)(A:E) : tipI (stalk l A) s=0:=by
 induction l generalizing s with
 | nil=> exact (p (by simp [ψS])).elim
 | cons i l ih=>
    have ht:s.Nodup:=List.Nodup.of_map σ t
    by_cases v:i∈s
    · obtain ⟨u,v',hx⟩:= List.append_of_mem v
      let D:=u++v'
      have hu:s.Perm (i::D):=hx ▸ List.perm_middle
      have hZ:= tipI (stalk l A) D; have hD:(σ i::D.map σ).Nodup:= (hu.map σ).nodup_iff.mp t
      change tipI (stalk _ A) s=_
      rw [show tipI _ _ = tipI (stalk (i::l) A) (i::D) from move_ζ hu (stalkR _ A) roots]
      have hF : Set.EqOn (cutI (stalk (i::l) A) i) (stalk l A ∘ dune i) (hill I):=by
         intro t ht; let K(w):= update t i w
         have he (w:ℂ):stalk (i::l) A (K w)=w • stalk l A (K w):=by simp [K,stalk,mul_smul]
         have hy:= mitt (stalkR (i::l) A) ht i; change HasDerivAt (fun w=> stalk _ _ (K w)) (cutI (stalk (i::l) A) i _) 0 at hy; simp_rw [he] at hy
         apply hy.unique; have hp:= (hasDerivAt_id' (0:ℂ)).smul (mitt (stalkR l A) ht i); rw [zero_smul,one_smul,zero_add] at hp; exact hp
      have hw:ψS σ D:=(List.nodup_cons.mp hD).2
      rw [show tipI (stalk (i::l) A) (i::D)=tipI (stalk l A∘ dune i) D from lace_C D hF roots,tip_V _ _ (List.nodup_cons.mp (hu.nodup_iff.mp ht)).1]; by_cases Q:ψS σ l
      · have hf:σ i∈l.map σ:=by by_contra hh; exact p (show (σ i::l.map σ).Nodup from List.nodup_cons.mpr ⟨hh,Q⟩)
        obtain ⟨j,g,e⟩:= List.mem_map.mp hf; have hp:j∉ D:=fun v=> (List.nodup_cons.mp hD).1 (e ▸ List.mem_map.mpr ⟨j,v,rfl⟩)
        rw [←tip_V j D hp]; apply Eq.trans _ (tip_0 D); refine congrArg (fun F: Key I→ E => tipI F D) ?_; funext z; change (_:ℂ) • A=0; apply Eq.trans _ (zero_smul ℂ A); refine congrArg (· • A) ?_; apply List.prod_eq_zero; exact List.mem_map.mpr ⟨_,g,update_self ..⟩ -- tune
      exact ih D Q hw
    rw [←tip_V i s v]; have he: stalk (i::l) A ∘ dune i=fun _=>0:=funext fun z=>by change ((List.map _ (i::l)).prod:ℂ) • A=_; simp [dune]
    rw [he,tip_0]
#print axioms noStem
end GJ
end YM.CF.Roots
end

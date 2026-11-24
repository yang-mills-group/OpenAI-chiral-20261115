import YM.SU5.FiniteGaugeData.Maypole.Hex
import ZecaGarden
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder



lemma siphon₀ {α β:Type} (f:α→β)(u v:List β)(h:u.Perm v) :
    ∀ t:List α,t.map f=u→∃ w:List α,w.Perm t ∧ w.map f=v:=by
  induction h with
  | nil=> exact fun t q=>⟨t,.refl _,q⟩
  | cons i p ih=>
    rintro (_|⟨a,t⟩) q
    · simp at q
    rw [List.map_cons] at q
    injection q with e k
    obtain ⟨w,v,g⟩:=ih _ k
    exact ⟨a::w,v.cons _,by rw [List.map_cons,g,e]⟩
  | swap i j v=>
    rintro (_|⟨a,-|⟨b,t⟩⟩) q
    · simp at q
    · simp at q
    rw [List.map_cons,List.map_cons] at q
    injection q with e k; injection k with k h
    exact ⟨b::a::t,List.Perm.swap _ _ _, by rw [List.map_cons,List.map_cons,h,k,e]⟩
  | trans p q ih jh=>
    intro t u; obtain ⟨w,v,k⟩:=ih t u
    obtain ⟨y,r,s⟩:=jh w k
    exact ⟨y,r.trans v,s⟩

open Poin Vp.Folio Mink General Lorentz
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:Bench S)
local notation "χ"=>Item G.Chip
local notation "ψ"=> wordValue S Ω.val G.dep G.grade

lemma siphon (D:G.Tile S Ω)(p:SO)(L L':List χ)
    (h:(Marked G p L).Perm L')
    (F:ahead timeAxis L)(e:ahead timeAxis L'): ψ L=ψ L':=by
  obtain ⟨n,f,x,rfl⟩:=e_pref L
  let y:=turnO p.val x; let g:=G.stampE p f
  rw [show Marked G p (mail x f (Each n))= mail y g (Each n) by unfold Marked mail; rw [List.map_map]; rfl] at h
  obtain ⟨w,v,t⟩:=siphon₀ _ _ _ h (Each n) rfl
  rw [← show mail y g w=_ from t] at e ⊢
  rw [peering,peering]
  exact D.turn n p x f _ _ (.refl _) v ((order_p ..).1 F) ((order_p ..).1 e)
#print axioms siphon

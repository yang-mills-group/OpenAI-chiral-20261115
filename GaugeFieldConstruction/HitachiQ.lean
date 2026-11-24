import GaugeFieldConstruction.CowrieQ
import GaugeFieldConstruction.Mapley
import GaugeFieldConstruction.WallabyQ
import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.BootHearthJ
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4200
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace WallsQ
open Weir
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "m" n:max s:max=>momentm Y n s
variable {i k:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(s:ℕ)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "sf" e:max=> sharp Y H s (π e) (ζ e)
variable {J:Type}[Fintype J]
variable {σ:Cover}{W n:ℕ}{G:J→ℝ}{o:J → Cover}{F:J→ℕ→Family (tent Y H)}{f:J→Family (tent Y H)}{S:J→Finset Cover}
def FireQ (e d:ℕ)(w:ℕ)(σ o:Cover)(F:Family (tent Y H))(p:ℝ):Prop:=∀ n:Side,CatellaQ K w σ n ((K).c (m e s))→∀ (L:List (dialQ n))(t:useinQ L)(V:dialQ n→Family K),(∀ x,TwigQ K w σ o F n x (V x))→ ‖sharp Y H s e d ((L.map V).prod)‖≤p^L.length
lemma ComplyQ (a:ℕ)(u:chute Y σ)(e:(W:ℤ)=westW Y a):∀ᶠ i:ℕ in atTop,∃ n:Side,CatellaQ (tent Y H) W σ n ((tent Y H).c (momentm Y i s)):=by
 filter_upwards [water_paid Y H σ u s a] with i ⟨n,h⟩; rw[← e] at h; obtain ⟨c,d,f⟩:=h; exact ⟨n,(by exact_mod_cast c),(by exact_mod_cast d),f⟩
lemma button_wind {u: Cover}{x:Cover}(p:u≠x) : ∃ c:ℕ,∀ n:Side, c ≤ n.val → buttonQ n u ≠ buttonQ n x:=by
 obtain ⟨j,p⟩:= Function.ne_iff.mp p -- tune
 let t:= u j - x j; refine ⟨t.natAbs+1,fun n h e=>?_⟩
 have g:0<t.natAbs:=Int.natAbs_pos.mpr (sub_ne_zero.mpr p)
 have hd: (↑(2*n.val):ℤ) ∣ t := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congrFun e.symm j)
 have hv:(2*n.val) ∣ t.natAbs:=by exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hd) -- tune
 have he:= Nat.le_of_dvd g hv; omega
lemma button_late (p:Injective o) (z:Tendsto i atTop atTop):∀ᶠ e:ℕ in atTop,∀ n:Side,CatellaQ (tent Y H) W σ n ((K).c (momentm Y (i e) s))→Injective (buttonQ n∘o):=by
 have h(x y:J):∀ᶠ e:ℕ in atTop,∀n: Side, CatellaQ (tent Y H) W σ n ((K).c (momentm Y (i e) s))→ (buttonQ n (o x)=buttonQ n (o y))→ x=y:=by
    by_cases w:x=y; · exact Eventually.of_forall (fun _ _ _ _=>w)
    obtain ⟨c,p'⟩:=button_wind (p.ne w)
    filter_upwards [((goes Y H s).comp z).eventually_ge_atTop (W*c)] with e hv n A H
    have ht:=A.2.1; rw[side_register Y _] at ht; apply False.elim (p' n (Nat.le_of_mul_le_mul_left (hv.trans ht.le) A.1) H) -- goes
 filter_upwards [eventually_all.mpr (fun x=>eventually_all.mpr (h x))] with e hv n p'; exact fun x y t=> hv x y n p' t
include Q V
lemma boardFireQ {L:List J}(jv:useinQ L)(h:∀ j,PipeQ K W σ (o j) (S j))(e:(W:ℤ)=westW Y n)(pσ:chute Y σ)(g:∀ j,BQueue (S j) (F j) (f j))(u:∀ j, 0≤ G j)(H':∀ j c,G j<c→∀ᶠ r:ℕ in atTop, FireQ Y H s (π r) (ζ r) W σ (o j) (F j r) c)(t:Injective o): ‖E s ((L.map f).prod)‖≤ (L.map G).prod:=by
 have hv(e₀:ℝ)(hv:0<e₀): ‖E s ((L.map f).prod)‖≤ (L.map (fun j=> G j+e₀)).prod:=by
    let G'(j:J):=G j+e₀/2; have hz(j): G j<G' j:=lt_add_of_pos_right _ (half_pos hv); have ht(j):0<G' j:=(u j).trans_lt (hz j); have hp(j):G' j<G j+e₀:= add_lt_add_right (by linarith) _
    let i':=fun r:ℕ=> π r; have hk:Tendsto i' atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    choose A A1 z v using fun j:J=> (g j).bdd
    obtain ⟨T,hq⟩:=Weir.drift_q (L:=L) S o f g
    apply le_of_tendsto (hot_deck Y H V s Q _ T hq).norm
    filter_upwards [Q.finance s,eventually_all.mpr v,eventually_all.mpr (fun j=> H' j (G' j) (hz j)), eventually_all.mpr (fun j=>screenFlash Y H V s Q (A j) (G' j) (G j+e₀) (A1 j) (ht j) (hp j)), hk.eventually (ComplyQ Y H s n pσ e),button_late Y H s (σ:=σ) (W:=W) t hk] with r δ y pr w ⟨d,hc⟩ b
    change ‖hot Y H s (π r) (ζ r) (wharf _)‖ ≤ _; rw [drift_pay]; unfold hot; rw[dif_pos δ.depth]
    let j':= π r; let k':= ζ r; let ε:=boxprice Y H (j') k' δ.depth s δ.fire δ.enters; have p(j):InTest K true (S j) false (F j r):= (g j).whereTo r
    apply SteamQ ε (fun j=>(ht j).trans (hp j)) p y h hc jv (b _ hc)
    intro j L t M K0
    have ht':0<L.length:=by rw[whyΨQ d L t]; have ht:= d.property; positivity
    have hm:L.length≤ (2*(Journey.side Y (π r) s).val)^4:=by rw [whyΨQ d L t, ←side_register Y H]; have hy: d.val ≤ ((tent Y H).c (momentm Y j' s)).val:= hc.2.1.symm ▸ Nat.le_mul_of_pos_left _ hc.1; gcongr
    let γ:= fun _ : dialQ d=> j
    have he:tentPegQ W σ (tent Y H) o (fun j=>F j r) d γ M:=K0 -- need Nonempty J
    letI:= show Nonempty J from ⟨j⟩
    obtain ⟨a,c⟩:= QuartzPayQ ε ht p y h he L
    have hp:L.map (A∘ γ)= L.map (fun _=>A j):= rfl; rw[hp,List.map_const',List.prod_replicate] at c
    have hp':= (w j L.length ht' hm _ a c).1 (pr j d hc L t M K0); unfold hot at hp'; rw [dif_pos δ.depth] at hp'; exact hp'
 have hg(L:List J):Continuous (fun c:ℝ=>(L.map (fun j=>G j+c)).prod):=by induction L with|nil=>exact continuous_const|cons j L ih=> exact (continuous_const.add continuous_id).mul ih
 have t:= ge_of_tendsto (((hg L).tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)) ((show ∀ᶠ x:ℝ in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin).mono hv)
 simpa using t
#check Function.ne_iff
#check goes
#check Int.natAbs_dvd_natAbs
#print axioms boardFireQ
end WallsQ
end YM.CF.Buffered.Afterglow.Tower.SlabMark
end

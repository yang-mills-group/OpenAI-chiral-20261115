import GaugeFieldConstruction.Mcc3
import GaugeFieldConstruction.Shoot
import GaugeFieldConstruction.SingingT
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
abbrev soloRoot (n:Side):=Support (More n)
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "K"=> Tenant.carrier
local notation "Y"=> Single n
local notation "G"=> LeanV (Single n)
def sip0 (S: Support (More n)): Op (Single n):= if S.card=1 then halfP S else 0
-- one kernel pointer
abbrev gainH(D:Support (More n)):Op (Single n):= sip0 S+ uplift F R k D S t W
abbrev giftH(D:Support (More n)):Op (Single n):=sip0 S-uplift F R k D S t W
abbrev χH(D:Support (More n)) : G→G→ℂ:=alter_M (gainH F R k t S W D) (giftH F R k t S W D)
abbrev rawH : G→G→ℂ:=alter_M (sip0 S+releaseQ F S (R W)) (sip0 S-releaseQ F S (R W))
lemma sip_e (i j:Single n): sip0 S i j= if S={aptK i} ∧ i=j then (1:ℂ)/2 else 0:=by
 unfold sip0; split_ifs with a b b
 · rw [halfP,Matrix.diagonal_apply]; rw [←b.2,b.1]; simp -- tune Ekm
 · by_cases q:i=j; · rw [←q,halfP,Matrix.diagonal_apply_eq]; exact if_neg (fun p=> b ⟨by
                        obtain ⟨x,hx⟩:=card_eq_one.mp a; rw [hx]; rw [show aptK i=x from (Finset.mem_singleton.mp (show aptK i ∈{x} from hx ▸ (show aptK i∈ S from p)))],q⟩) -- tune orientation tactic layout
   rw [halfP,Matrix.diagonal_apply]; rw [if_neg q]
 · exact False.elim (a (b.1 ▸ card_singleton _))
 · rfl
variable (u:Roof n t d k R)(p:0<d)
include u p
private lemma gains_r {E:Op (Single n)}(V:∀ i j,E i j≠0 → aptK i∈S∧aptK j∈S) (i j:LeanV (Single n))(v:alter_M (sip0 S+ E) (sip0 S-E) i j ≠0) : i∈camp S∧ j∈ camp S:=by
 obtain ⟨b,i⟩:= i; obtain ⟨l,j⟩:=j; have hp(b:Bool)(i:Single n)(u:aptK i∈S): (b,i)∈ camp S:= mem_filter.mpr ⟨mem_univ _,u⟩
 cases b<;>cases l
 · exact False.elim (v rfl)
 · by_cases t:E i j=0; swap; · exact ⟨hp _ i (V i j t).1,hp _ j (V i j t).2⟩
   change sip0 S i j-E i j ≠0 at v; rw [sip_e,t,sub_zero] at v; split at v; next b=> rw [b.1,b.2]; simp [camp, aptK,Tenant.carrier,Cube.node, helix] -- tune
   contradiction
 · by_cases t:E j i=0; swap; · exact ⟨hp _ _ (V _ _ t).2,hp _ _ (V _ _ t).1⟩
   change sip0 S j i+E j i ≠0 at v; rw[sip_e,t,add_zero] at v; split at v; next h=> rw [h.1,h.2]; simp [camp, aptK,Tenant.carrier,Cube.node,helix]
   contradiction
 · exact False.elim (v rfl)
lemma chin_i (i j:G)(q:χH F R k t S W D i j≠0): i∈camp S∧j∈camp S:= by
 apply gains_r R k t S u p _ i j q
 intro a b q; have hz:= lift_real (F:=F) u p a b (D:=D) (S:=S) (U:=W); exact ((F.coat S|>.1 ()|>.expo a b).triggered (ne_of_gt ((norm_pos_iff.mpr q).trans_le hz))).2
lemma raw_i (i j:G)(q:rawH F R S W i j≠0): i∈ camp S∧ j∈camp S:=by
 apply gains_r R k t S u p _ i j q; intro i j h; rw [re_L F S _ (u.paid _) p] at h; let Z:= (F.coat S).1 ()|>.expo i j; exact (Z.triggered (ne_of_gt ((norm_pos_iff.mpr h).trans_le (Z.bounded _)))).2
section
-- local transfer requirements off meta.Release.
lemma Symψ (s:pure_Rim F): star (uplift F R k D S t W)=uplift F R k D S t W:=by
 unfold Sour.SliceRoof.uplift; split; exact releaseHerm s _ S (u.paid _) p; exact star_zero _
private lemma sipH : star (sip0 S)=sip0 S:=by unfold sip0; split; exact half_H _; exact star_zero _
lemma gauge_γ (g: Agora n)(r:pure_Rim F): let Y': Orbit n:=(GA g W.1,threadG g W.2); let L:=tradew n g; Altaz L false false (gainH F R k t S W D) (giftH F R k t S W D) (gainH F R k t S Y' D) (giftH F R k t S Y' D):=by
 intro Y' L; let Λ:= sip0 S; have ht: star Λ= Λ:= sipH R k t S u p -- args
 have he:twist L Λ= Λ:=by unfold Λ sip0; split; exact half_frame ..; exact map_zero _
 have h0:= Symψ F R k t S D W u p r; have hp:uplift F R k D S t Y'= twist L (Vx W):= lift_gZ u p _
 refine ⟨?_, ?_, ?_,?_⟩
 · rw [gainH,star_add,ht,h0]
 · rw [giftH,star_sub,ht,h0]
 · change twist L (Λ+_) =Λ+SliceRoof.uplift _ _ _ _ _ _ _; rw [map_add,he,hp]
 · change twist L (Λ-_) =Λ-SliceRoof.uplift _ _ _ _ _ _ _; rw [map_sub, he,hp]
lemma movedΥ (s:Sweep n)(z:groupShape F)(r:pure_Rim F)(u0:Injective (priorP W.2)):
 let W':Orbit n:= (flashA s W.1,bun s W.2);
 let L:=launchZ s
 Altaz L s.charge (detX s.s) (gainH F R k t S W D) (giftH F R k t S W D) (gainH F R k t (actY s S) W' (actY s D)) (giftH F R k t (actY s S) W' (actY s D)):=by
 intro W' L; let Y':=Vx W; let Z:= SliceRoof.uplift F R k (actY s D) (actY s S) t W'; let b:=detX s.s; let p':=s.charge
 let A:=sip0 S; let T:=sip0 (actY s S)
 have ht: star A= A:=sipH R k t S u p
 have hp: twist L (windX s.charge A)= T:=by
    unfold A T sip0; rw [show (actY s S).card=S.card from card_map ..]; split
    · rw [half_w,show twist L _=_ from half_motion S s]
    rw [win_z,map_zero]; -- zero requirement
 have hk: star Y'=Y':=Symψ _ _ _ _ _ _ _ u p r
 have he:star (twist L (windX p' Y'))=twist L (windX p' Y'):=by rw [←map_star,←win_s,hk]
 have hZ:Z= if b then -twist L (windX p' Y') else twist L (windX p' Y'):=by
    rw [show Z=realR s true Y' from lift_move u p s u0 z]; unfold realR; change Thera.jazz (detX s.s) (twist L (windX p' Y')) = _; unfold Thera.jazz; rw [he]
 refine ⟨?_,?_,?_,?_⟩
 · unfold gainH; rw[star_add,ht,hk]
 · unfold giftH; rw[star_sub,ht,hk]
 · change twist L (windX p' (A+Y'))= if b then T-Z else T+Z; rw[win_a,map_add,hp,hZ]; split_ifs <;> simp only [sub_neg_eq_add]
 · change twist L (windX p' (A-Y'))=if b then T+Z else T-Z; rw[win_l,map_sub,hp,hZ]; split_ifs <;> simp only [sub_eq_add_neg]
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end

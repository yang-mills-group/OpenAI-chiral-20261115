import YM.CF.Cour.Culm
import YM.CF.Stake.Male
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.CF.Stake
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc MeasureTheory Urn Hake Levier
open Fir Matrix Phase
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
open Pec Cour
variable {j n k:ℕ}{N P B L:Side}{a C d e δ r s f g:ℝ}{t:Odd L.val}{R:Pricing j L t (Thread j)}{U:Grasp R B e}{G: Ratio (CSide N B) (CSide P B)}
local notation "Q"=> QuotaH r s f g
local notation "K"=> arcB r s f g
local notation "α"=> CSide N B
local notation "β"=> CSide P B
local notation "F₁"=> Levier.mineB G
local notation "Y₁"=> Levier.mineC G
structure GuideB (t:Odd G.count.val)(i:QuotaH r s f g)(Kf:Aim (CSide P B))(U':Meter TailB G e)(V:Meter Grave G e)(a c y:ℝ)(j m:ℕ):Prop where
 lead:(i.1 _).val=Kf
 meter:∀ t:TailB, OccuS G e true false m (G.count.val:ℝ)⁻¹ a (population*(c*followV [] G.count)) (U' t)
 cost:∀ t:Grave, Bisca G e true true a (population*y) (heal G e V t)
 worn: Levier.aura G e U'
 gone: Levier.hue G e V
 issue (Z:Rent0 G e) (Y:Bkg (More (CSide P B)))(p: Guard Y e)(x:cro G e) (h:x.val=(unionP Z.val,Tulip.profile Y)):fulfills G t e (j:=j) Prod.snd (arcB r s f g) i U' V x
variable (A:QuotaH r s f g)(p:Odd G.count.val)
local notation "ZB"=> Levier.mineB G p e (j:=j) Prod.snd K A
local notation "ZC"=> Levier.mineC G p e (j:=j) Prod.snd K A
set_option maxHeartbeats 800000 in
lemma end_a(u:1 ≤ j)(h:0<e)(T:Pearl U)(W:Stamped j L t R)(X:U.roundZ≤ (CSide N B).val)(y:G.count=L)(Z: Rent0 G e)(Y:Bkg (More (CSide P B)))(v:Guard Y e)(D: Reef.Cry (A.1 β|>.val))(hx:Hops G j t (A.1 β|>.val) A.2 Z.val) (x:cro G e) (l:x.val=(unionP Z.val,Tulip.profile Y)) : chillF G e x=x ∧ (∀ k:Sweep (CSide N B),(∀ i,toSpin G k (ZB i x)= ZB (liftA i (accent k)) (toWish G e k x)) ∧ ∀ i,toSpin G k (ZC i x)= ZC (flingX i (accent k)) (toWish G e k x)) ∧ KindX (Urn.soar (oakN G (fun i=>ZC i x))) :=by
 subst L; obtain ⟨T1,T2,T3⟩:=hx
 have he(Yw:Rent0 G e):∀ i, Along j G.count p (Thread j) i A.2 G (unionP Yw.val):=by
    obtain ⟨v,hv⟩:= Phase.cue_from Yw.val.2; let U':=Brace.starfish N B Yw.val.2 v; have ht:=pose_g U h G rfl X _ Yw.property U' (Brace.starK U.capY h.le Yw.property.cg hv); exact (R.cap G rfl (U.needed.trans X) A.2 _ ht.glyph).chart
 obtain ⟨e',k⟩:=desire_c (j:=j) (o:=p) A Z.val _ rfl
 have h₁:IsUnit (1+nuke G.count p j K Prod.snd A G (unionP Z.val)):=by rw [←e']; exact nearOne (by simp only [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]; exact T1)
 have h₂:IsUnit (1+nukeR j K Prod.snd p A G (unionP Z.val)):=by rw [←k]; exact nearOne (by simp only [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]; exact T2)
 refine ⟨?_,fun z=> ?_,?_⟩
 · apply Subtype.ext; change (icec x.val.1,ice x.val.2)=x.val; rw [l]; exact Prod.ext (revI ..) (ice_pr ..)
 · have hp:=(he Z); let W':=A.1 (CSide P B); have hv:= peak_f W'.val (Pec.den_r W'.property) D (Shape.broad G (castX z)) z.charge (spinU z.charge z.s) (spinZ ..) Z.val.1; have hV(i l₀):= Vow (j:=j) G p e z Prod.snd K A x Z.val Y l (W.fields_one _ (U.needed.trans X)) (W.fields_one _ (U.needed.trans (U.clock_fine G X))) (v.shrink U.gem) (ampleB Z.property U.gem) u (fun b y v=>v.elim (fun g=>g.symm ▸ hp b) (fun y=> y.symm ▸he (male e G z Z) b)) T3 (by unfold arcB; rw [Moire.bloom_P,Moire.bloom_P]; exact hv) h₁ h₂ i l₀
   exact ⟨fun i=>(hV i (false,false,false,false)).1, fun i=>(hV (false,false) i).2⟩
 let z:=U.broadness _ (U.clock_fine G X) A.2; exact enKind G p e Prod.snd K A Z.val Y x l (carts_p (switchG G).symm (z.projection _ v)) (he Z true) h₁
end YM.CF.Stake

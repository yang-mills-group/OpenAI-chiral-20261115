import YM.CF.Stake.Stance
import YM.CF.Stake.Gate
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
abbrev CutP(t:Odd L.val)(j n:ℕ)(r s f g z c e:ℝ)(m:ℕ):Prop:=∀ x:ℝ,0<x→x≤e→∀ i:TailB,∀{N P:Side}(G:Ratio N P),G.count=L→m≤N.val→∀ h:Odd G.count.val,∀ v:QuotaH r s f g, Street (badge _) (pinH G x true) (pinH G x false) n (G.count.val:ℝ)⁻¹ z (fun _=>c*followV [] G.count) (mineB (j:=j) G h x Prod.snd (arcB r s f g) v i)
abbrev CutZ(C:ℝ)(j n:ℕ):Prop:=0<C ∧∀ (L:Side)(t:Odd L.val)(r s f g:ℝ),0<r→0<s→0≤f→0≤g→∃ z e:ℝ,0<z∧0<e∧∃ m,CutP t j n r s f g z C e m
lemma granted(j n:ℕ)(h:2≤ j)(p:Even j):∃ C:ℝ,CutZ C j n:=by
 obtain ⟨C,u,H⟩:= legWide n h p; refine ⟨C,u,fun L t r s f g a b w c=>?_⟩; obtain ⟨l,z,p,h,m,S⟩:= H L t _ _ Prod.snd (alum w c a b).1 (alum w c a b).2
 refine ⟨z,l,h,p,m,fun x u v i N P G hg n o t'=>?_⟩; have hx:= S x u v i (mem_univ _) G hg n o t'; subst L; exact hx
lemma gates(p:CutZ C j n)(h:Even j)(w:2 ≤ j)(u:0<r)(v:0<s)(t':0≤f)(e':0≤g)(L:Side)(k:Odd L.val): ∃ a d e:ℝ,0<a∧0<d ∧0<e ∧ ∃ N:ℕ,∀ {x B},∀ {R:Pricing j L k (Thread j)}{U:Grasp R B x},Stamped j L k R →Pearl U →0<x→x≤ e →∀ {m P:Side}{G:Ratio (CSide m B) (CSide P B)},G.count=L → max N U.roundZ ≤ (CSide m B).val →∀ z:Odd G.count.val,∀ (A: QuotaH r s f g)(V:Aim (CSide P B)),(A.1 _).val=V →Reef.Cry V → (∀ y:Rent0 G x,Hops G j k V A.2 y.val) → ∃ X Y,GuideB (e:=x) z A V X Y a C d j n:=by
 obtain ⟨Z,e,hZ,hE,N,F⟩:= p.2 L k r s f g u v t' e'; obtain ⟨W,D,E,hW,hD,hT,N',Y'⟩:=legC L k j w h _ Prod.snd (alum t' e' u v).1 (alum t' e' u v).2
 let b:= min Z W; refine ⟨b,D,min e E,lt_min hZ hW,hD,lt_min hE hT,max N N', fun {x B R U} z y t v {m P G} i p j' A V hJ gX T=>?_⟩
 have hp:max N N' ≤ (CSide m B).val:= (le_max_left ..).trans p; have hh:0 ≤ (G.count.val:ℝ)⁻¹:=by positivity
 obtain ⟨U₁,U₂,o,q,rX,w',T'⟩:= picture G j' x Prod.snd K A n _ b _ D (j:=j) (fun i'=> (F _ t (v.trans (min_le_left ..)) i' G i ((le_max_left ..).trans hp) j' A).desc (min_le_left ..) hh) (fun i'=> (Y' x t (v.trans (min_le_right ..)) A G i ((le_max_right ..).trans hp) j' i').drop (min_le_right ..)) hh
 refine ⟨U₁,U₂,hJ,o,q,rX,w',fun Z Y v x H=>?_⟩; subst V; obtain ⟨A',I,S⟩:=end_a _ j' (by omega) t y z ((le_max_right ..).trans p) i Z Y v gX (T Z) x H; exact T' x A' I S
end YM.CF.Stake

import YM.CF.Gully.Mold
import YM.CF.Ione.Tape
import YM.CF.Spire.Thick
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {a v b c d:ℝ}
open Scion Skye Hive Ione Scree
open Skye Scion Ione Tulip
section
variable {hp:1≤H}{j:ℕ}{o:Odd L.val}{T:Pricing j L o (Thread j)}{P:Grasp T B e}{Y:Briar m B e→ Ewe m B}
structure Fire_ins (Z:Scroll m B (northZ m B))(k:ℝ)(P:Grasp T B e)(n:ℕ)(K H a d:ℝ):Prop where
 slate :∃ W:Briar m B e→ Cipher Λ, PlotQ K n H e W a d∧ ∀ i,∀ Y: FC (Single Λ), (∫ z, ratioRF Z e 0 k 1 (northZ m B) (fun _=>Spark.crossL (helix _).symm Y) (i.val,z)∂rains m)=inner ℂ (mateK Λ) (acts Y (setD P i (W i)))
lemma coastZ (X:Spire.Pearl P)(V:Stamped j L o T)(h:1≤ j)(t:0<e)(g:P.roundZ ≤ (CSide m B).val)(l:∀ i:Briar m B e,∀ s:Era m,Rayp s B (Y i)=Y (shotV s i))(k:ℝ):plaza fun i:Briar m B e=>Marsh m B (CordQ P k i (Y i)):=by
 intro s i; change Marsh m B _= suit_Y _ _; rw [← lingQ]; apply congrArg; unfold CordQ; rw [map_add,map_add,rayZX,wax_z X V h g t,map_smul,rayZX, l]; have he:payZ s (energ m B (northZ m B) i.val)= energ m B (northZ m B) (shotV s i).val:=by rw [earn_H s i P.baseY]; unfold payZ; cases wageZ s; rfl; exact realFlight P.baseY i _
 rw [he]
lemma lit_ins (aQ:0<a)(Z:Scroll m B (northZ m B))(k:ℝ)(X:Spire.Pearl P)(V:Stamped j L o T)(h:1≤j)(p0:P.roundZ ≤(CSide m B).val)(t:0<e)(g:HatX e H hp U n Y a v)(f:∀ i:Briar m B e, (motor (Ave.travel m B e H hp) (fun w=>exp (chillT Z k w)) i)=exp (Y i)∧∀ s:Era m,Rayp s B (Y i)=Y (shotV s i))(c':HatX (m:=m) e H hp U n (fun x=>hollow (candle m B (P.cost m firstM) x.val)) a c)(d':HatX (m:=m) e H hp U n (fun x=>hollow (energ m B (northZ m B) x.val)) a d)(l:Δt n K U): Fire_ins Z k P n K H a (c+(‖k‖*d+v)):=by
 let W(i:Briar m B e):= CordQ P k i (Y i); have ht : HatX e H hp U n W a (c+(‖k‖*d+v)):= unite_L c' (unite_L (scale_L d' k) g)
 exact ⟨Marsh m B ∘ W,yearZ (hold_C ht) l (coastZ X V h t p0 (fun i=>(f i).2) k), fun i y=>chord_D Z k i (f i).1 P p0 y⟩
end
lemma cant_X (K:ℝ)(q:1≤K)(n:ℕ):∃ σ A a G:ℝ,0<σ ∧ σ<1∧0<A∧0<a∧0<G∧∃ N:ℕ,∀ B:Side,N≤ B.val→∃ d e:ℝ,0< d∧0<e∧(∀ v:ℝ,0<v→v≤e→ Budget B v d)∧(∀ m:Side, ∃ W:Scroll m B (northZ m B), GripK W A a G)∧∀ (w:ℝ),0<w→ w≤e→∀ (j:ℕ){L:Side}(o:Odd L.val)(T:Pricing j L o (Thread j))(P:Grasp T B w)(p':Spire.Pearl P)(Y:Stamped j L o T),1 ≤ j→∃ c C G':ℝ,0<c∧0 ≤ C∧0 ≤ G'∧∀ h:ℝ,∀ u:1≤h,∀ᶠ k:ℕ in atTop,∀ m:Side,P.roundZ ≤ (CSide m B).val→∀ W:Scroll m B (northZ m B),GripK W A a G→ Fire_ins W k P n K (bond σ h k) c (C+(k*G':ℝ)):=by
 obtain ⟨U,s,W⟩:=μt n q; obtain ⟨σ,A,a,G,C,p,y,u,v,x,w,M,N⟩:=harvest_F (P:=2) (by norm_num) s n; obtain ⟨R,h⟩:=coin_s n s (r:=1) zero_lt_one
 refine ⟨σ,A,a,G,p,y,u,v,x,M+R,fun B l=>?_⟩
 obtain ⟨d,g,t,b,f,L',ρ,h0,T⟩:=N B (by omega); obtain ⟨Z,qZ,X⟩:= h B (by omega); obtain ⟨Z',hZ,Q⟩:=nozz n (P:=2) (by norm_num) h0 w
 refine ⟨d,g,t,b,L',f,fun e e' G' j L o T' P p' Y g=>?_⟩
 obtain ⟨b,g',b',pS,L''⟩:=wax_m p' Y g e' n s
 let c:=feeG B.val; have hc:0<c:=by unfold c feeG; positivity
 let c':=min b (1/c); let C':= feeG 2; have hk:0<c':=lt_min b' (one_div_pos.mpr hc); have hv:0 ≤ C':=by unfold C' feeG; positivity
 refine ⟨c',g'+ C'*Z',C'*Z,hk,by positivity,mul_nonneg hv qZ,fun z l=>?_⟩; filter_upwards [T z l] with k A' m g'K B' U1 -- tune
 obtain ⟨k',K'⟩:= A' e e' G' p' Y g m g'K B' U1; obtain ⟨F,F',X0⟩:= Q _ _ _ _ _ B' _ _ K'; rw [show (2:ℝ)/2=1 by norm_num] at F'
 have he:= purse (L'' m g'K (bond σ z k) k') (min_le_left b (1/c)) le_rfl; have ht:= purse (elevate_C F' zero_le_one hZ) (min_le_right b _) le_rfl; have hy:= purse (elevate_C (X _ _ _ k' P.baseY (northZ m B)) zero_le_one qZ) (min_le_right b _) le_rfl
 have hx:= lit_ins hk B' k p' Y g g'K e' ht X0 he hy W
 convert hx using 1; rw [Real.norm_of_nonneg (by positivity:0 ≤ (k:ℝ))]; unfold C'; ring
end YM.CF.Gully

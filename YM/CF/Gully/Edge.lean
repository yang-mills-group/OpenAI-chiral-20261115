import YM.CF.Gully.Fibre
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
variable (s:Era m)
local notation "C"=> netB m B s
lemma wing_T (b:Sweep N)(x:Cipher N) (Y:ℝ): dilF Y (suit_Y b x)=suit_Y b (dilF Y x):=by
 let X:=dilF Y (suit_Y b x); let V:= suit_Y b (dilF Y x); apply Subtype.ext; change X.val=V.val; rw [(fineShape X).allP, (fineShape V).allP]; apply sum_congr rfl; intro i hi; change crumb X.val i • poke i=crumb V.val i • poke i; apply congrArg (fun d:ℂ=>d • _); unfold X V; rw [dil_p,roseQ,roseQ,mul_sum]; refine sum_congr rfl fun j _=>?_; rw [dil_p]; by_cases h: (hail_Q b).val i j=0; · simp only [h,zero_mul,mul_zero]
 rw [inkE b i j h]; unfold payZ; cases wageZ b<;> simp [cSignX,mul_left_comm] -- tune
lemma shot_m(s t:Era m)(x:Briar m B e): shotV t (shotV s x)=shotV (s*t) x:=Subtype.ext (by change flashA _ (flashA _ _)=flashA _ _; rw [lights,map_mul])
lemma roll_O(s t:Era m)(X:Stamp m B): actS (netB m B t) (actS (netB m B s) X)=actS (netB m B (s*t)) X:=by rw [map_mul,actG_s] -- C notation local shadow s
def Δt (n:ℕ)(H' H:ℝ):Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](m B:Side)(e:ℝ)(s:Era m)(F:E→ Briar m B e)(x:E), TransK n (fun i=>(F i).val) x H' → TransK n (fun i=>(shotV s (F i)).val) x H
lemma μt (n:ℕ)(l:1≤ K):∃ U:ℝ,1≤ U∧Δt n K U:=by
 obtain ⟨U,w,h⟩:= tutor K n l; refine ⟨_,l.trans w,fun E _ _ _ m B e s F x v=> ?_⟩
 let V:=netB m B s; apply (h (CSide m B) (castX V) s.charge E (fun i=>(F i).val) x (fun _=>vacuumW _) v ?_).1; intro i; apply allows_const; simpa only [hookN] using l -- tune seek

abbrev Oil(m B:Side):= Stamp m B→ Briar m B e→ Cipher (CSide m B)
def linkQ(s:Era m)(S:Stamp m B):=actS (netB m B s) S -- implicit B tune
variable {S:Stamp m B}
def RainD(s:Era m)(F:Briar m B e→ Cipher Λ)(x:Briar m B e): Cipher Λ:= suit_Y (netB m B s)⁻¹ (F (shotV s x))
lemma bar_d {F:Briar m B e→Cipher (CSide m B)}(h:Inscribed U e n (linkQ s S) H F a)(t:Δt n K U): Inscribed K e n S H (RainD s F) a:=by
 let c:=C; let r(x):= shotV (B:=B) (e:=e) s x; have hc:= (suit_Y c⁻¹).toLinearMap.continuous_of_finiteDimensional; have he(X:Stamp m B):actS c⁻¹ (actS c X)=X:=actG_l c X; let T:=linkQ s S
 refine ⟨h.pos,fun a=> he S ▸ grove_t _ _ (h.grove a),fun i=> he S ▸ (rich_F c⁻¹ _ _ (h.grammar (r i))),fun i x=>?_,fun i j t=> ?_,hc.comp (h.continuous_T.comp ?_),?_⟩
 · unfold RainD
   have hu: shotV s (routeS x i)=routeS ((polarT c.charge ∘ x) ∘ (castX c).anon Λ) (shotV s i):=by apply Subtype.ext; exact revG c i.val x
   rw [hu,h.gauge]
   exact gauge_E c x (F (shotV s i))
 · refine congrArg (fun x:Cipher Λ=>suit_Y c⁻¹ x) (h.locality (r i) (r j) (flashD c i.val j.val T ?_)); rwa [show T.map (boxA c).toEmbedding=S by ext; simp [T,linkQ,c,actS]] -- tune T.map function meta
 · change Continuous (fun x:Briar m B e=>shotV s x); apply Continuous.subtype_mk; exact (revM c).comp continuous_subtype_val
 intro E _ _ _ f V p k y l; simp_rw [RainD,wing_T]; let g:= r ∘ f; have hp:= h.jets E g V p (fun i l=> t E m B _ s f i (k i l)) y l; let Z:Cipher Λ →L[ℝ] Cipher Λ:=⟨(suit_Y c⁻¹).toLinearMap,hc⟩; rw [←one_mul a]; refine Allows.linear (F:=Cipher Λ) (G:=Cipher Λ) Z hp ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; change ‖sings _ _ x.val‖ ≤ ‖x.val‖; exact (singN ..).le
lemma layer {F:Briar m B e→Cipher (CSide m B)} (S:Stamp m B)(z:ℝ)(h:Inscribed U e n S H F a): Inscribed U e n S H (fun i=>z • F i) (‖z‖*a):=by
 refine ⟨mul_nonneg (norm_nonneg _) h.pos,fun v=>h.grove (right_ne_zero_of_mul v),fun i=>  ?_,fun x t=>?_,fun x y t=>congrArg _ (h.locality x y t),(continuous_const (y:=z)).smul h.continuous_T,?_⟩
 · change z • F i ∈ Pastry.stretch _; apply Subalgebra.smul_mem; exact h.grammar i
 · rw [h.gauge,map_smul]
 intro E _ _ _ f V p q x t; simp only [map_smul]; exact ((h.jets E f V p q x t)).smul z
lemma stem_V{I:Type}[Fintype I]{A:I→ Briar m B e→ Cipher Λ}{x:I→ℝ}(p:∀ i,Inscribed U e n S H (A i) (x i)): Inscribed U e n S H (fun j=>∑ i,A i j) (∑ i,x i):=by
 refine ⟨sum_nonneg (fun i _=>(p i).pos),fun h=>?_ ,fun i=>?_,fun i t=>?_,fun i j v=>sum_congr rfl (fun z _=>(p z).locality i j v),continuous_finsetSum _ (fun i _=>(p i).continuous_T),?_⟩
 · obtain ⟨x,y,l⟩:= exists_ne_zero_of_sum_ne_zero h; exact (p x).grove l
 · apply (Pastry.stretch (camp S)).sum_mem (fun z _=>(p z).grammar i) -- tune
 · rw [map_sum]; exact sum_congr rfl fun x _=> (p x).gauge i t
 intro E _ _ _ f V p' q y h; simp_rw [map_sum]; exact allows_sum (fun i _=>(p i).jets E f V p' q y h)
end YM.CF.Gully

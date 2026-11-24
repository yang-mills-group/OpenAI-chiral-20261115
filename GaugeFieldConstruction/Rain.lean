import GaugeFieldConstruction.Hops
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedVariables false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes Tenant Phase.Sample
variable {K b c d r v e a:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=> CSide m B
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
abbrev Baro (K e:ℝ)(n:ℕ)(R:Support (More N))(A:Pane N→X)(c:ℝ): Prop:=0≤c ∧ ContinuousOn A (Clode N e)∧ (∀ x∈Clode N e,∀ y∈ Clode N e, Agrees R x y→ A x=A y) ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E→ Pane N)(x:E),U x∈ Clode N e → TransK 7 U x K→ Allows n (A ∘ U) x c
variable {V:Stamp m B}{F:Pantry m B→X}
local notation "H_"=> Clode Λ e
abbrev densP(x:Pantry m B):= law m B x.1 x.2
abbrev Cloud(F:Pantry m B→X)(x:Skin m B):= ∫ y:Cue m, densP (x,y) • F (x,y) ∂Phase.rains m
abbrev shelter (e:ℝ)(x:Clode (CSide m B) e × Cue m):Pantry m B:= (x.1.val,x.2)
lemma Ka.gifts (h:Ka K n e V F c)(p:1≤K):Gift (densP ∘ shelter (m:=m) (B:=B) e) (F∘ shelter e) c:=by
 have he:Continuous (shelter (m:=m) (B:=B) e):=(continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
 have hel(x:Clode Λ e × Cue m): 0≤(densP ∘ shelter (m:=m) (B:=B) e) x:= sails_nonneg (rock m B x.1.val) univ x.2
 apply soft hel _ ((law_cont m B).comp he) -- implicit lean
 · rintro ⟨x,y⟩ t; have he':shelter e (x,y)∈ Lobby m B e:= ⟨x.property,t⟩; exact (h.ct _ he'|>.continuousAt (lobby_o.mem_nhds he')).comp he.continuousAt
 rintro ⟨x,y⟩ g; exact (h.track ℝ (fun _=> x.val) 0 y ⟨x.property,g⟩ (fun i=> allows_const _ ((CStarRing.norm_of_mem_unitary (SU.fund_U ..)).trans_le p))).value
lemma Ka.weather_R (h:Ka K n e V F c)(p:1≤K){x:Skin m B}(u:x∈ Clode Λ e):Continuous fun i:Cue m=> fall (rock m B x) i • F (x,i):=(h.gifts p).weighted.comp (f:=fun i:Cue m=> ((⟨x,u⟩:Clode (CSide m B) e),i)) (continuous_const.prodMk continuous_id)
variable [CompleteSpace X]
lemma Ka.Cloud_ct (h:Ka K n e V F c)(p:1≤K):ContinuousOn (Cloud F) (Clode Λ e):=by
 letI : LocallyCompactSpace (Clode Λ e) := IsOpen.locallyCompactSpace isOpen_interior
 apply continuousOn_iff_continuous_restrict.mpr; exact (h.gifts p).settled (μ:=Phase.rains m) -- tune
lemma Ka.Cloud_eq (h:Ka K n e V F c)(p:1≤K){x:Skin m B}{y:Skin m B}(u:x∈ Clode Λ e)(s:y∈Clode Λ e)(e':Agrees V x y): Cloud F x= Cloud F y:=by
 refine banks_like (rock m B x) (rock m B y) (fun i=>F (x,i)) (fun i=> F (y,i)) (complex_down m B V) (complex_down m B V) ?_ ?_ (h.weather_R p u) (h.weather_R p s)
 · intro z; apply prod_congr rfl; intro i g
   have ht: room m B i ⊆ V:= (mem_filter.mp g).2; exact water_limit _ _ i z z (fun _ _=>rfl) (fun i a b=>e' i (ht a) (ht b)) -- room namespace tune
 intro i j k a b; exact h.watch (x,i) ⟨u,a⟩ (y,j) ⟨s,b⟩ e' k
abbrev τFuel (K b:ℝ) (B:Side):Prop:=∀ (m:Side) (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](S:Set E),IsOpen S→∀ (U:E→Skin m B), (∀ x∈S, TransK 6 U x K)→ Jet.FireK S (rock m B ∘ U) b 6
lemma billed_FK (B:Side)(p:1≤ K):∃ C:ℝ,0≤C ∧ τFuel K C B:= Jet.ryth 6 K B p
lemma Ka.Cloud_out (h:Ka b 6 e V F d)(hc:1≤ b)(p:b>K)(hp:τFuel b c B)(hx: 0≤ c): Baro K e 6 V (Cloud F) (mercury (complexA m B V).card 6 c d):=by
 refine ⟨le_trans h.pos (Jet.bigger _ _ h.pos hx),h.Cloud_ct hc,fun _ u _ s=>h.Cloud_eq hc u s,fun E _ _ _ U x p' H=>?_⟩
 have he:∀ᶠ t in 𝓝 x, U t∈ Clode Λ e ∧ TransK 7 U t b:= ((cliff_n H).eventually (isOpen_interior.mem_nhds p')).and (stream_T H p)
 obtain ⟨S,s,p,hx⟩:=_root_.mem_nhds_iff.mp he; have hr(i)(v:i∈S):U i ∈ Clode Λ e∧TransK 7 U i b:=s v
 refine Jet.waitB (hp m E S p U (fun x p i=> ((hr x p).2 i).order (by decide))) (fun x t=>F (U x,t)) (complexA m B V) (fun _ _=>complex_down m B V) (fun t x p v=>h.track E U x t ⟨(hr _ p).1,v⟩ (hr _ p).2) h.pos (fun x p t u x' y' hv=>h.watch _ ?_ _ ?_ ?_ hv) (fun x v=> h.weather_R hc (hr _ v).1) x hx
 · exact ⟨(hr _ p).1,x'⟩
 · exact ⟨(hr _ p).1,y'⟩
 exact fun _ _ _=>rfl
lemma rains_eq (F: SheetT m B)(g:Pane Λ→ℂ)(u:∀ x∈ Lobby m B e, F x=g x.1)(x:Pane Λ)(p:x∈ Clode Λ e): Cloud F x=g x:=by
 unfold Cloud; rw [←one_smul ℝ (g x)]; nth_rw 1 [← Phase.rain_law m B x]; rw [←integral_smul_const]; apply integral_congr_ae; filter_upwards with y; by_cases h:densP (x,y)=0; change _ = densP (x,y) • _; rw [h,zero_smul,zero_smul]; change densP (x,y) • F _=_ ; rw [u _ ⟨p,h⟩]
-- ↑ shelter cost calibrates finite.Volume.
abbrev Mon (K a C:ℝ):Prop:=∀ (m B:Side) (V:Stamp m B) (A:ℝ), 0≤ A → Branch.rent (a/2) V *mercury (complexA m B V).card 6 K A ≤ C*(Branch.rent a V*A)
lemma keepMon (p:0≤K)(h:0<a):∃ C:ℝ,0≤ C ∧ Mon K a C:=by obtain ⟨C,q,s⟩:=Jet.stash K p 6 h; exact ⟨C,q,fun m B V A v=>s A v V.card (complexA m B V).card (rate_cap _)⟩ -- order card
lemma sumrain {T:Type*}[Fintype T](g:SheetT m B)(A:T→ SheetT m B)(q:Stamp m B)(S:T→Stamp m B)(p:T→ℝ)(h:∀ i,Ka K 6 e (S i) (A i) (p i))(s:∀ x∈ Lobby m B e,g x=∑ i,A i x)(v:1≤ K) {x:Skin m B}(u:x∈Clode Λ e): Cloud g x=∑ i,Cloud (A i) x:=by
 unfold Cloud; rw [←integral_finsetSum]; apply integral_congr_ae; filter_upwards with y; by_cases p:densP (x,y)=0; simp [p]; rw [s _ ⟨u,p⟩,Finset.smul_sum];
 intro i _; exact Phase.net_compact ((h i).weather_R v u)
section
abbrev ABox (K a C e:ℝ)(R:Stamp m B)(F:Skin m B→ℂ):Prop:=∃ (P:Stamp m B→ Skin m B→ℂ)(q:Stamp m B→ℝ),(∀ V, Baro K e 6 (N:=CSide m B) V (P V) (q V)∧ (q V≠0→ Grove (Tenant.terr _) V∧ R⊆ V)) ∧ ∑ V,Branch.rent a V*q V ≤ C ∧ ∀ x∈Clode Λ e,F x=∑ V,P V x
abbrev QBox (K a C e:ℝ)(R:Stamp m B)(F:Pane (CSide m B)→ Op (Single (CSide m B))):Prop:=∃ (P:Stamp m B→ Pane Λ→ Op (Single Λ))(q: Stamp m B→ Toll (Single Λ)), (∀ V i j,Baro K e 6 V (fun x=> P V x i j) (q V i j) ∧ (q V i j≠0→ Grove (terr _) V ∧ R⊆ V ∧ aptK i∈V ∧ aptK j∈V))∧ costM a q ≤ C ∧∀ x∈Clode Λ e, F x=∑ V,P V x
variable {F0:SheetT m B} {W:MSheet m B}{Q:Stamp m B}{C:ℝ} (h:τFuel K b B) (p:1≤K)(w:v<K)(tb:0≤b)(D:Mon b a C) -- C declare
include h p w tb D
lemma Scribes.cost_r (u:Scribes K 6 e a d Q F0)(g:0≤C): ABox v (a/2) (C*d) e Q (Cloud F0):=by
 obtain ⟨V,q,t,z,u⟩:=u; let k(S:Stamp m B):=mercury (complexA m B S).card 6 b (q S); refine ⟨fun x=> Cloud (V x),k, fun S=>⟨(t S).1.Cloud_out p w h tb, fun p'=>?_⟩,(sum_le_sum fun i _=> D _ _ i _ (t i).1.pos).trans (by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left z g),fun x p'=> sumrain F0 V Q id q (fun x=>(t x).1) u p p'⟩
 apply (t S).2; intro v; apply p'; unfold k mercury; rw [v]; ring
abbrev polar_C (W:MSheet m B)(x:Pane (CSide m B)): Op (Single Λ):= Matrix.of fun i j=> Cloud (fun x=> W x i j) x
lemma HitM.cost_k (u:HitM K 6 e a d Q W)(g:0 ≤ C): QBox v (a/2) (C*d) e Q (polar_C W):=by
 obtain ⟨q,V,t,u,E⟩:=u; let k(S:Stamp m B) (i j):=mercury (complexA m B S).card 6 b (q S i j); refine ⟨fun S=> polar_C (V S),k,fun V i j=>⟨(t V i j).1.Cloud_out p w h tb, fun p=>?_⟩,?_,fun x e=> ?_⟩
 · apply (t V _ _).2; intro v; apply p; unfold k mercury; rw [v]; ring
 · apply le_trans _ (mul_le_mul_of_nonneg_left u g); unfold costM k saleM; simp_rw [mul_sum]; apply sum_le_sum; intro i _; apply sum_le_sum; intro j _; apply sum_le_sum; intro S _; exact D _ _ _ _ (t S i j).1.pos
 ext i j; rw [Matrix.sum_apply]; exact sumrain _ (fun S x=> V S x i j) Q id (fun S=>q S i j) (fun x=>(t x i j).1) (fun x u=> by change W x i j=_; rw [E x u,Matrix.sum_apply]) p e -- tune congrArg
end
end YM.CF.XGarden
end

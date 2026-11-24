import GaugeFieldConstruction.Abbas
/- choose root derivative receipt Z_j on actual Λ with cap budget. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d t r u c h a b h0:ℝ}{j k:ℕ}{m B n:Side}
namespace MastTin
open Shield Echo Ledger Jet
local notation "GS"=> SU.group
local notation "Λ"=> CSide m B
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable (o:Seat n) {X:Hubber n}{p:BudgetPoint}
def isolate (i:Wa n)(f:Lit n):Paper n:=Pi.single i f
lemma publish (i:Wa n)(f:Lit n)(A:Pane n):marketD (isolate i f) A=f A • dot_Q i:=by
 unfold marketD isolate; rw [sum_eq_single i]
 · simp
 · intro l _ h; rw [Pi.single_eq_of_ne h]; simp
 simp
lemma moorage(i:Wa n)(v:DomainP X i)(f:Lit n)(q:Micro p X f c): TrackD p X h (isolate i f) (papW n h i*c):=by
 refine ⟨Pi.single i c,fun l=>?_,?_⟩
 · by_cases p:l=i
   · subst l; exact ⟨by simpa [isolate] using q, fun k=> (k v).elim⟩
   exact ⟨by simp only [isolate,Pi.single_eq_of_ne p]; exact micro_Z, fun _=> Pi.single_eq_of_ne p _⟩
 apply le_of_eq; rw [sum_eq_single i]
 · simp
 · intro k p v; simp [v]
 simp -- indent
lemma isolate_z (i:Wa n):isolate i (0:Lit n)=0:=Pi.single_zero _
variable {A:Paper n}
lemma explore(u:Dock o X)(h1:TrackD p X h A c): TraceD p o h a (Pi.single X A : Flounces n) (rent a X*c):=by
 refine ⟨Pi.single X c,fun i=>?_,?_⟩
 · by_cases p:i=X
   · subst i; simp only [Pi.single_eq_same]; exact ⟨h1,fun k=>(k u).elim⟩
   simp only [Pi.single_eq_of_ne p]; exact ⟨track_zero,fun _=>True.intro⟩
 apply le_of_eq; rw [sum_eq_single X]
 · simp
 · intro k p v; simp [v]
 simp
abbrev ρperk (a:ℝ)(j:ℕ):= a/ (((j+8)+(j+8)+1:ℕ)^4:ℕ)
lemma perk_pos (h:0<a)(j:ℕ):0<ρperk a j:=by unfold ρperk; positivity
lemma rent_policy(h:0≤a): rent (ρperk a j) (Sect X j) ≤ rent a X:=by
 apply Real.exp_monotone
 unfold ρperk; rw [div_mul_eq_mul_div]; refine (div_le_iff₀ (by positivity)).mpr ?_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h; exact_mod_cast Corona.halo_size X (j+8)

section endum
variable {e:ℝ}{R:Loom n}(v:Roof n u e k R) (d':e < d) (T:Ids n)(kT:hud_T 7 K)(g:1≤K)(s:p.threshold≤u)(w:p.order≤6)
variable (S:Hubber n)(F: Lit n)(P:Baro K d 6 S F c)
include v d' T g w kT s P
lemma houseT : Micro p (Sect S k) (kiosk S k u R T F) c:=⟨P.1,arm_Env S F v T d' P g,arm_loc S F v T d' P,fun i h=> arm_milk S F v T d' P p i h s kT w⟩
omit s kT w
lemma houseZ (l:c=0): kiosk S k u R T F=0:=by
 funext i; unfold kiosk; split; swap
 · rfl
 let A:= R (i,T); apply norm_le_zero_iff.mp; rw [←l]; exact (P.2.2.2 ℝ (fun _=>A) 0 (grow_I (v.paid _) d') fun i=> allows_const _ ((CStarRing.norm_of_mem_unitary (SU.fund_U ..)).trans_le g)).value
include s kT w
lemma house_f (h':0≤a)(z:Wa n)(Y:c≠0→ Dock o S ∧ DomainP (Sect S k) z) : TraceD p o h (ρperk a k) (Pi.single (Sect S k) (isolate z (kiosk S k u R T F))) (rent a S*(papW n h z*c)):=by
 by_cases q:c=0
 · rw [houseZ v d' T g S F P q,isolate_z,Pi.single_zero,q,mul_zero,mul_zero]; exact trace_Z
 obtain ⟨u,h⟩:=Y q
 exact trace_p (explore o ⟨halo_subset _ _ u.1,crown_H u.2 _⟩ (moorage z h _ (houseT v d' T kT g s w S F P))) le_rfl (mul_le_mul_of_nonneg_right (rent_policy h') (mul_nonneg (papW_v _) P.1))
end endum
variable {O:Skin m B} {L:Side}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P: Grasp Y B d}
section Z
open Push.Mark Brace
variable (o:Seat (CSide m B))(l:Axis)(A:inkMus)
local notation "E" => (at_E o l (musk A))
abbrev letter (M:Flounces n):Paper n:=∑ i:Hubber n,M i
abbrev totalE(o:Seat n)(M:Flounces n):=marketD (letter M)
lemma receipt_env(o:Seat n){B0:BudgetPoint}(p:Flounces n)(u:TraceD (p:=B0) (a:=a) (h:=h) o p c) : Envelope (totalE o p):=by
 obtain ⟨V,q,h⟩:=u; change Envelope (marketD (∑ x,p x)); rw [conn_X, show (∑ i, marketD (p i))=_ from funext fun x:Pane n=> Finset.sum_apply x univ fun i=>marketD (p i)]; exact Env.total _ (fun i=> val_T (q i).1) -- meta budget
lemma roots_dist(X:Hubber n)(A:Paper n): marketD (letter (show Flounces n from Pi.single X A))=marketD A:=by simp [letter]
variable {f r: ℝ}{p:BudgetPoint}{R:Loom (CSide m B)}(v:Roof _ t f k R)(hU:f<d)(T:Ids (CSide m B))(tK:hud_T 7 K)(hK:1≤K)(s:p.threshold≤ t)(w:p.order≤6)(ha:0<a)
include v hU T tK hK s w ha
lemma reactive (x:QBox K a u d (m:=m) (B:=B) (ends (o,l)) (Legume (m:=m) (B:=B) E j))(y:ABox K a r d (m:=m) (B:=B) (ends (o,l)) (decl P m E))(V:∀ x∈Clode (CSide m B) d, let ψ:=changeM P x firstM; HasDerivAt (fun i:ℝ=>changeM P (bud E x i) firstM) (acts (dg (Legume (m:=m) (B:=B) E j x)) ψ + decl P m E x • ψ) 0∧ (decl P m E x).re=0):
 ∃ M:Flounces (CSide m B), TraceD p o h (ρperk a k) M (r+h^2*u) ∧ ∀ U∈tight p (CSide m B), HasDerivAt (fun i:ℝ=>changeM P (turnLink (o,l) (musk A) i U) firstM) (acts (totalE o M U) (changeM P U firstM)) 0:=by
 obtain ⟨D,Vc,U1,U2,U3⟩:=x; obtain ⟨H,W,wH,hW,eW⟩:=y; let L(i l:Single (CSide m B))(X:Hubber (CSide m B)): Paper (CSide m B):=isolate (some (true,i,l)) (kiosk X k t R T fun x=> D X x i l); let G(i):=isolate none (kiosk i k t R T (H i))
 let b(i):Flounces (CSide m B):=Pi.single (Sect i k) (G i); let a'(i j:Single Λ)(X:Hubber (CSide m B)):Flounces Λ:=Pi.single (Sect X k) (L i j X); let B0:= ∑ i,b i; let At:=∑ i:Single Λ,∑ j':Single Λ,∑ X:Hubber Λ,a' i j' X
 have hb(i):TraceD p o h (ρperk a k) (b i) (rent a i*W i):=by
    have hh:= house_f (a:=a) (h:=h) o v hU T tK hK s w i _ (wH i).1 ha.le none (fun e=> ⟨⟨((wH i).2 e).2 (by unfold Skye.ends; exact mem_insert_self ..),((wH i).2 e).1⟩,True.intro⟩)
    change TraceD _ _ _ _ _ (rent a i*(1*W i)) at hh; rw [one_mul] at hh; exact hh
 have hx(i j:Single Λ)(X:Hubber Λ):TraceD p o h (ρperk a k) (a' i j X) (rent a X*(h^2*Vc X i j)):=by
    apply house_f o v hU T tK hK s w _ _ (U1 X i j).1 ha.le (some (true,i,j)); intro n; obtain ⟨x,u,A0,H0⟩:= (U1 X i j).2 n; exact ⟨⟨u (mem_insert_self ..),x⟩,halo_subset _ _ A0,halo_subset _ _ H0⟩
 have he:TraceD p o h (ρperk a k) At (h^2*u):=by
    apply trace_p (trace_sum univ _ (fun i=> ∑ j:Single Λ,∑ X:Hubber Λ, rent a X*(h^2*Vc X i j)) (fun i _=> trace_sum univ _ (fun j=>∑ X:Hubber Λ, rent a X*(h^2*Vc X i j)) fun j _=> trace_sum univ _ _ fun X _=> hx i j X)) le_rfl; simp_rw [mul_left_comm (rent _ _), ←mul_sum]; exact mul_le_mul_of_nonneg_left U2 (by positivity) -- sale
 refine ⟨At+B0, trace_p (trace_u he (trace_p (trace_sum univ b (fun i=> rent a i*W i) fun i _=>hb i) le_rfl hW)) le_rfl (add_comm _ _).le,fun i p=>?_⟩ -- shadow
 have hp': flags _ i=∅:=p; have hp:=Ledger.top_strict v hU hp' s; have hy:= (V i hp).1; simp_rw [one_link]; apply hy.congr_deriv -- reorder
 have hv{I:Type} [Fintype I](F:I→Flounces Λ): marketD (letter (∑ i,F i))=∑ i,marketD (letter (F i)):=by rw [show letter _=_ from (show letter (∑ i,F i)=∑ i,letter (F i) from ?_),conn_X]; unfold letter; simp_rw [Finset.sum_apply]; rw [sum_comm] -- sum_apply for functions flounces
 let W:=Legume (B:=B) (m:=m) E j i
 let V:= decl P m E i
 have hM: marketD (letter At) i=dg W:=by
    unfold At; simp_rw [hv,Finset.sum_apply,show ∀ j k X,marketD (letter (a' j k X))= marketD (L j k X) from fun _ _ _=>roots_dist ..]; unfold dg dyad; rw [show W=∑ V,D V i from U3 i hp]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; rw [Matrix.sum_apply, Finset.sum_smul]; apply sum_congr rfl; intro q _; unfold L; rw [publish, arm_eq _ _ v T hU (U1 q j k).1 i hp' s]; rfl -- k shadow!
 have hN:marketD (letter B0) i= V • (1:FC (Single Λ)):=by
    rw [show B0=∑ i,b i from rfl,hv,Finset.sum_apply,show V=∑ q,H q i from eW _ hp,sum_smul]; apply sum_congr rfl; intro x l; rw [show marketD (letter (b x))=marketD (G x) from roots_dist ..]; unfold G; rw [publish,arm_eq _ _ v T hU (wH x).1 i hp' s]; rfl
 let ψ:=changeM P i firstM; unfold totalE; rw [show letter (At+B0)=letter At+letter B0 from (by unfold letter; simp_rw [Pi.add_apply,sum_add_distrib]),conn_a,Pi.add_apply,hM,hN,act_add,act_smul,act_one]
end Z
end MastTin
end YM.CF.XGarden
end

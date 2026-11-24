import YM.SU5.Lamour.Ferry
import YM.SU5.Velvet.Heather
/-!
# price from (center/bag, correct local orientation on this Pane). group things that depend on geometry separately and DO NOT require cross chart cohesion.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 150000
noncomputable section
namespace YM.CF.Lamour
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side}{a j d r:ℕ}{e ε δ z:ℝ}{P:Pane N}{T:Finset (Seat N)}
-- dimensions cost
section cols
variable {n:Type*} [Fintype n][LinearOrder n][Nonempty n] {A:Op n} {S:Finset n}
def Wat (S:Finset n)(X:Op n)(u:ℝ):Prop:=∀ i∈S,‖acts X (basisKet i)‖≤u
lemma cash_cut (h:‖A*cutM S‖≤e): Wat S A e:=by intro i p; have ht:=opy (A*cutM S) (basisKet i); rw [act_mul,cut_basis,if_pos p] at ht; simpa using ht.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
lemma cut_bill (p:0≤e)(h:Wat S A e):‖A*cutM S‖ ≤ S.card*e:=by
 let X:=A*cutM S; rw [←Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x; change ‖acts X x‖≤ _; let Y(i):=x.ofLp i • acts X (basisKet i)
 nth_rw 1 [←basis_expand x]; rw [map_sum]; simp_rw [map_smul]; change ‖∑ i,Y i‖≤ _; rw [←sum_subset (subset_univ S)]; swap; · intro i _ q; unfold Y X; rw [act_mul,cut_basis,if_neg q,map_zero,smul_zero]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>‖x‖*e) (fun i q=>?_)).trans_eq ?_)
 · have ht: ‖x.ofLp i‖≤ ‖x‖:=by rw [←basis_inner]; exact (norm_inner_le_norm ..).trans (by simp)
   unfold Y X; rw [act_mul,cut_basis,if_pos q,norm_smul]; exact mul_le_mul ht (h i q) (norm_nonneg _) (norm_nonneg _)
 rw [sum_const,nsmul_eq_mul]; ring
lemma pcut (x:Ket n)(S:Finset n): ‖acts (cutM S) x‖≤ ‖x‖:= (opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _))
lemma measure_col {P:Op n}(i:n) (x:Finset n): ‖acts (cutM x*P) (basisKet i)‖^2=∑ j∈x,‖P j i‖^2:=by
 rw [act_mul,EuclideanSpace.norm_sq_eq,←sum_subset (subset_univ x)]; swap; · intro j _ e; change ‖(acts _ _).ofLp j‖^2=0; rw [cut_apply,if_neg e]; simp
 exact sum_congr rfl fun j q=>by change ‖(acts _ _).ofLp j‖^2=_; rw [cut_apply,if_pos q,basis_act]
lemma Wat.add' {P Q:Op n}(h:Wat S P e)(g:Wat S Q ε): Wat S (P+Q) (e+ε):=fun i l=>by rw [act_add]; exact (norm_add_le ..).trans (add_le_add (h _ l) (g _ l))
end cols
variable (j z N)(M:Male)(P:Pane N)
def here:= draft (spar j M P) (tickA N) z
def fleece(b:Bool): Op (Single N):= wish (tickA N) (here N j z M P) z b
variable {j z N M P}
lemma mica(g:Seat N→SU.E)(q:Sparkle N δ M j)(p:0<z)(t:z≤1)(h:Guard P δ): let s:=tradew N g; let V:=Lattice.gauge g P
 sill N j M z V=twist s (sill N j M z P) ∧∀ b:Bool,fleece N j z M V b= twist s (fleece N j z M P b):=by
 intro s V; have he:twist s (tickA _)=tickA _:=Tfree ..; have hx:= account_cov q h g p t; constructor
 · unfold sill slant; rw [hx,map_smul,map_mul,map_mul,map_sub,he,map_one]
 intro b; unfold fleece wish here; rw [hx,map_smul,map_mul,handAgainst,handAgainst,he]
-- dale ledger T vs star X
namespace Bridge
variable (j z)
def impale(b:Bool):LedgerK:=let S:=sky; let D:=account j z; let X:=if b then S*D*(1-S) else (1-S)*D*S; fun r N M V=>(z^2)⁻¹ • X r N M V
def cog(b:Bool):LedgerK:=fun _ N M P=> fleece N j z M P b
variable {j z} {g:Guard P δ}
lemma truePol (c:0<z)(t:z≤1)(s:Sparkle N δ M j)(p:Guard P δ)(b:Bool)(ρ: Rails): impale j z b ρ N M P= if b then star (sill N j M z P) else sill N j M z P:=by
 cases b; rfl
 let D:=here N j z M P; let S:=tickA N; let T:=(z^2)⁻¹; have h:=Kea.cut_t N
 change T • (S*D*(1-S))=star (T • ((1-S)*D*S)); rw [star_smul,star_trivial,star_mul,star_mul, h.one_sub.isSelfAdjoint,h.isSelfAdjoint, (show star D=D from (draft_lit (s.projection P p) h c t).1.isSelfAdjoint.star_eq),mul_assoc] -- tune
lemma prudentV (p:Procurement j a δ)(h:0<z)(s:z≤1)(b:Bool): Prudence a δ (impale j z b) :=by
 let Q:=p.insp; let e:= Prudence.tick (δ:=δ) (n:=a); let u:=flowing p h s; cases b; exact (((Prudence.id.sub' e).mul' u Q).mul' e Q).scalec Q _; exact ((e.mul' u Q).mul' (Prudence.id.sub' e) Q).scalec Q _
lemma prudentQ (p:Procurement j a δ)(h:0<z)(s:z≤1)(b:Bool): Prudence a δ (cog j z b) :=by
 let Q:=p.insp; let e:= Prudence.tick (δ:=δ) (n:=a); let u:=flowing p h s; cases b; exact ((Prudence.id.sub' u).mul' e Q).scalec Q _; exact (u.mul' (Prudence.id.sub' e) Q).scalec Q _
structure ClothQ (a j:ℕ)(δ z e:ℝ)(v:ℝ)(u:ℕ):Prop where
 raiseP : ∀ b, Strands a δ (impale j z b) e v u
 costUp : ∀ b, Strands a δ (cog j z b) e v u
lemma mold_phase (p:Procurement j a δ)(h:0<z)(s:z≤1)(v:0<e):∃ u:ℝ,0<u∧ ∃ r:ℕ, ClothQ a j δ z e u r:=by
 have ht(b:Bool):∃ u:ℝ,0<u ∧∃ r:ℕ,Strands a δ (cog j z b) e u r∧Strands a δ (impale j z b) e u r:=by obtain ⟨l,t,d,L⟩:= (prudentQ p h s b).clean e v; obtain ⟨x,g,y,H⟩:= (prudentV p h s b).clean e v; exact ⟨min l x,lt_min t g,d+y,L.up (Nat.le_add_right ..) (min_le_left ..) le_rfl, H.up (Nat.le_add_left ..) (min_le_right ..) le_rfl ⟩
 obtain ⟨u,v',w,a₀,b₀⟩:= ht true; obtain ⟨x,f,y,a₁,b₁⟩:=ht false; let d0:= Nat.le_add_right w y; let d1:=Nat.le_add_left y w; let w0: min u x≤u:=min_le_left ..; let w1:min u x≤x:=min_le_right ..; exact ⟨min u x,lt_min v' f,w+y,(fun b=>by cases b; exact b₁.up d1 w1 le_rfl; exact b₀.up d0 w0 le_rfl),(fun b=>by cases b; exact a₁.up d1 w1 le_rfl; exact a₀.up d0 w0 le_rfl)⟩
def Closen (j:ℕ)(z ε:ℝ):Prop:=∀ (N:Side), Kea.Pad j N→∀ M, Glaze.Billow ε (sill N j M z 1-lake N j M)∧ ∀ b,Glaze.Billow ε (fleece N j z M 1 b)
lemma cab(p:1≤j)(u:0<e):∀ᶠ z:ℝ in 𝓝[>] 0,Closen j z e:= pollen p e u
/-- wind bound inside one clear register. post orientation. -/
structure Clear (T:Finset (Seat N))(P:Pane N)(j:ℕ)(M:Male)(z ε:ℝ):Prop where
 reach : Wat (modesIn N T) (sill N j M z P-lake N j M) ε
 fetch : Wat (modesIn N T) (star (sill N j M z P-lake N j M)) ε
 yarn : ∀ b:Bool,Wat (modesIn N T) (fleece N j z M P b) ε
variable {S:Finset (Seat N)}
local notation "Λ" => modesIn N S
theorem purchase (p:Procurement j a δ)(h:0<z)(t:z≤1)(v:Kea.Pad j N)(u:a≤N.val)(w: ClothQ a j δ z e ε r)(c: Closen j z e)(x:Guard P δ)(y:Rightful (Lattice.halo r S) P 1 ε)(M:Tulip.Male): Clear S P j M z (e+e) :=by
 let V:= sill N j M z; let B:= lake N j M; let X:= P; let _r:Rails:= ⟨0,Set.left_mem_Icc.mpr zero_le_one⟩
 have hz:= p.audit (M:=M) u; have hp:=c N v M; let D:=Λ; let K:= cutM D; have hv(b:Bool): Wat D ((if b then star (V P) else V P)-(if b then star (V 1) else V 1)) e:=by
    have he:= (w.raiseP b _r N M P u x).2 S y; rw [truePol h t hz x,truePol h t hz (guard0 p.insp)] at he; exact cash_cut he
 refine ⟨by convert (hv false).add' (P:= V P -V 1) (Q:=V 1-B) (fun i _=> (hp.1 i).1) using 1; abel,?_,fun b=>?_⟩ -- convert susceptible simplify
 · rw [star_sub]; have hu:= (show Wat D (star (V 1)-star B) e from (by rw [←star_sub]; exact fun i _=> (hp.1 i).2)); have he:= (show Wat D (star (V P)-star (V 1)) e from hv true); rw [show star (sill N j M z P)-star (lake N j M)= (star (V P)-star (V 1))+(star (V 1)-star B) from (by unfold V B; abel)]; exact he.add' hu
 let U:= fun P=>fleece N j z M P b; have ht:‖(U P-U 1)*K‖≤e:=(w.costUp b _r N M P u x).2 S y; change Wat _ (U P) _; rw [←sub_add_cancel (U P) (U 1)]; exact (cash_cut ht).add' (fun i _=>(hp.2 b i).1)
end Bridge
end YM.CF.Lamour
#print axioms YM.CF.Lamour.Bridge.purchase
#print axioms YM.CF.Lamour.Bridge.mold_phase

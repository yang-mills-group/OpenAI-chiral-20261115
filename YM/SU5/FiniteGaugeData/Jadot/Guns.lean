import YM.SU5.FiniteGaugeData.Jadot.Dolors
import YM.SU5.FiniteGaugeData.Jadot.Selle
import YM.CF.Buffered.Bouillon
import YM.CF.Buffered.Duels
/-! # Renewal invariant over harvested stamps. Raw foliage. Price & charge book. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 550000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade Dial Spire Paige Vault
open Avenue RouteM Spindle
open Rhythm Pilot PhaseM Steve VolumeRate
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Reduction.Dinar Reduction.Dijon Reduction.Rheims Fock.Brique Reduction.Dijon.Currency Reduction.Celeste Window.Presidio
open Reduction.Loyd Reduction.Loyd.Art Window.Presidio.Nigra Window.Presidio.Gato Fock.Relief Turnist
open Moorend YM.SU5.FiniteGaugeData.CodaT
open Alts
namespace Alts
variable {n:Side}{X:Orbit n}{P M D Y Z:Op (Single n)}{k b a s t C G ξ α w ε ε' δ μ v c r τ u:ℝ}{m i j d ℓ z:ℕ}{S S' T:Support (More n)}{U:Loom n}{q:Mark n}{g:Mosquito n}
local notation "Θ"=> tickA n
local notation "Γ"=> Single n
local notation "Ω"=> modesIn n
variable {Ξ ΘP:FC (Single n)} {V W:Finset (Single n)}
abbrev psiL (A:FC (Single n)):=‖acts (star A) (mateK n)‖
lemma pairF (S T:Finset (Single n))(p:Fock.Sector S false Ξ)(h:Fock.Sector T false ΘP)(D:Disjoint S T): psiL (Ξ*ΘP)= psiL Ξ*psiL ΘP :=by
 let i:= mateK n; have he(Ξ:FC (Single n)):((psiL Ξ)^2:ℝ)=(inner ℂ i (acts (Ξ*star Ξ) i)).re:=by unfold psiL; rw [act_mul,←act_inner]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
 have ht(Ξ:FC (Single n)): (Ξ*star Ξ) (Tset n) (Tset n)= ((psiL Ξ:ℝ):ℂ)^2:=by rw [←Cache.mateV_emit (Ξ*star Ξ),act_mul,←act_inner,inner_self_eq_norm_sq_to_K]; rfl
 have hA:Fock.Sector S false (Ξ*star Ξ):= p.mul p.contr; have hB:Fock.Sector T false (ΘP*star ΘP):= h.mul h.contr
 apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp; rw [he, show Ξ*ΘP*star (Ξ*ΘP)=Ξ*star Ξ*(ΘP*star ΘP) from ?_,show i=mateK n from rfl, Cache.mateV_emit, Sector.sliced hA hB D,ht,ht,←mul_pow,←Complex.ofReal_mul,←Complex.ofReal_pow]; rfl
 have hx:ΘP*star ΘP*star Ξ=star Ξ*(ΘP*star ΘP):=by simpa only [Sector.grainB,Bool.false_eq_true,Bool.and_false,ite_false,one_smul] using hB.apart p.contr D.symm -- tune
 rw [star_mul,mul_assoc,←mul_assoc ΘP, hx,mul_assoc]
-- Refund at every stamp.Soften_charge & sector. Charge after accounting even if many seats in halo.
namespace Emblem
variable (A:Emblem n P m d t s k C ξ G) (K:Currency (tickA n) P μ ε δ w s M D)
local notation "P₀"=>stageL V Θ P μ M
local notation "Q₀"=>stageZ W Θ P μ D
abbrev leanPay (α ξ C s k ε δ:ℝ)(m ℓ:ℕ):= (α+ξ+C+ Shill s (investK m) (investZ m ℓ) ε δ *k+k^2/2)
abbrev mHook (m ℓ:ℕ)(ε δ:ℝ):= (ε* investK m+δ*investZ m ℓ)
include A -- K conflict name.L.Fix
lemma rough_plus (g':CoversU X U z b t v g)(u:d≤z)(e:0≤G)(c:0≤ C): (Volt (tickA n) P (A.X (gauge g X.1))).re ≤ ξ+C+ Post.blight X b z (Emblem.rep A ℓ j)*G:=by
 let S:= Emblem.rep A ℓ j; let W:= gauge g X.1; let T:=discE X.1 b z ∩ S
 by_cases t_: T.Nonempty
 · have he:1 ≤ (T.card:ℝ):= by exact_mod_cast (show 1≤ T.card from card_pos.mpr t_)
   exact (A.rough W).trans (by change ξ+G≤ ξ+C+ (T.card:ℝ)*G; nlinarith only [he,mul_le_mul_of_nonneg_right he e,c]) -- tune
 have h: fieldR A.S t W:=by
    let P:= coverN X.1 b z (coreN z); let i:=A.existsS.choose; have hh:i∈A.S:=A.existsS.choose_spec
    have hv: i∈P:=by by_contra l; apply t_; exact ⟨i,mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,l⟩, (Subset.trans (halo_subset ℓ A.S) (halo_subset j _)) hh⟩⟩
    obtain ⟨y,e,Y⟩:=mem_biUnion.mp hv; let S':= Spindle.patch (η z) y; have h:A.S⊆S':=fun j v=>Avenue.extend y i j ((A.span i hh j v).trans u) Y; intro f t' v; exact (g'.beds y e).2.2.1 f (mem_filter.mpr ⟨mem_univ _,h t',h v⟩)
 exact (A.soaks _ h).trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) e))
abbrev tickets (g:Mosquito n)(X:Loom n)(i:Orbit n)(W:Mark n):= twist (quantU (tradew n g)) (W (Advance.drawn X i))
include K
lemma cozy (Y:Currency (tickA n) P 0 ε δ u s M D) (p:Standing (tickA n) P)(v':CoversU X U z b t v g)(u:d≤z)(e:0≤G)(c:0≤ C)(w: Ω A.S ⊆ V)(h:Ω (Lattice.halo ℓ A.S) ⊆ W)(gT: Neighbor ℓ M)(pT:Neighbor j D)(pS:0≤ s): let L:=stageL V Θ P μ M; let Z:=stageZ W Θ P μ D; let x:=Fock.Reduction.Celeste.cost L Z (tickets g U X (logoW A α)); Fock.Sector (Ω (Emblem.rep A ℓ j)) false x ∧ psiL x≤ Real.exp (leanPay α ξ C s k ε δ m ℓ+ Post.blight X b z (Emblem.rep A ℓ j)*G):=by
 intro L Z x; let i:= leanPay α ξ C s k ε δ m ℓ; let y:=Post.blight X b z (Emblem.rep A ℓ j)*G; let a:=A.X (gauge g X.1); let l:=Lattice.halo ℓ A.S; let b:= Lattice.halo j l; let T':= A.logoW α; let ρ:=Celeste.cost L Z a; have hx:x=((Real.exp α:ℝ):ℂ) • (1+ρ):=by
    let U_:=tradew n g; let t:=X.1; let c:ℂ:=Real.exp α; have hp:tickets g U X T'=c • (1+a):=by
       change twist (quantU U_) (c • (1+A.X t)) =c • (1+A.X (gauge g t)); rw [A.colored, twist_scalar,map_add,map_one]
    change Celeste.cost L Z (tickets g U X T') = _; rw [hp]; unfold Celeste.cost; have hw:= Pall.mun (K.buildL (S:=V) (monograph _|>.symm)) (K.buildZ (T:=W) (monograph _|>.symm)); have hh:= mul_eq_one_comm.mp hw; rw [Celeste.lever.semi hw hh, Celeste.lever.sums hw hh,Celeste.lever.stockI hw hh]
 -- syntax `unfold x`
 have he := Art.sameRoom (A.stocked (gauge g X.1)); have ht: ( (Ω l).card:ℝ) ≤ investZ m ℓ:=by exact_mod_cast tagZ (d:=ℓ) A.pays
 have hg: ( (Ω A.S).card:ℝ) ≤ investK m:=by exact_mod_cast snout A.pays
 have hz: Fock.Sector (Ω b) false ρ:= art_sector_build (N:=n) K (T:=l) le_rfl le_rfl w h gT pT hg pS (A.stocked _)
 rw [hx]; refine ⟨(Sector.one.add hz).scale _,?_⟩; change psiL _ ≤ Real.exp (i+y); unfold i leanPay; have hh1:=A.rough_plus (j:=j) (ℓ:=ℓ) v' u e c; unfold psiL; rw [star_smul,act_smul,norm_smul,norm_star,Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
 have hk := venture (k:=k) (S:=A.S) (T:=l) (U:=b) K p Y le_rfl le_rfl w h gT pT hg ht pS (A.stocked (gauge g X.1)) -- spacing
 have hw:= Pall.mun (K.buildL (S:=V) (monograph _|>.symm)) (K.buildZ (T:=W) (monograph _|>.symm)); have hh:= mul_eq_one_comm.mp hw; unfold BraWeight Celeste.cost at hk; rw [Celeste.lever.sums hw hh,Celeste.lever.stockI hw hh] at hk
 refine (mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le).trans ?_; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; unfold y; linarith only [hh1] -- unfold binder b shadows in y
end Emblem
open Emblem
namespace Flush
variable (pP:Fable P (tickA n))(U':CoversU X U z b t v g)(u':d≤z)(he:0≤G)(p':0≤ C)(K0:Currency (tickA n) P μ ε' δ w s M D)(Y':Currency (tickA n) P 0 ε' δ u s M D) (R':Neighbor ℓ M)(SBoost:Neighbor j D) (ps:0≤ s)
include pP U' u' he p' K0 Y' R' SBoost ps
-- harvest post upper all of Interest S. ticket i. even.
lemma Lease (h:Flush P m d ℓ j t s k C ξ G α i S q) : ∃ A B:Finset (Single n), A.card ≤ i*investK m ∧ B.card≤ i*investZ m ℓ ∧ ∀ V W:Finset (Single n), A⊆V→ B⊆W→ let Q:= Celeste.cost (stageL V Θ P μ M) (stageZ W Θ P μ D) (tickets g U X q); Fock.Sector (Ω S) false Q ∧ psiL Q ≤ Real.exp (i*leanPay α ξ C s k ε' δ m ℓ+Post.blight X b z S*G):=by
 let G_:= g; let cost0 (V W:Finset (Single n))(q:Mark n):= Celeste.cost (stageL V Θ P μ M) (stageZ W Θ P μ D) (tickets g U X q); let v:= leanPay α ξ C s k ε' δ m ℓ; let Y(S:Support (More n)):=Post.blight X b z S
 induction h with
 | piece A'=>
    let S:=A'.S; let U:=Lattice.halo ℓ S; refine ⟨Ω S,Ω U, by simpa only [one_mul] using (snout A'.pays), by simpa only [one_mul] using (tagZ A'.pays), fun i z y Z=> ?_⟩; simpa only [Nat.cast_one,one_mul] using A'.cozy K0 Y' pP.tender U' u' he p' y Z R' SBoost ps -- tune
 | unit V=>
    refine ⟨∅,∅,by simp,by simp, fun A B _ _=>?_⟩; change Fock.Sector (Ω V) false (cost0 A B 1) ∧ psiL (cost0 A B 1) ≤ _; have hw:= Pall.mun (K0.buildL (S:=A) (monograph _|>.symm)) (K0.buildZ (T:=B) (monograph _|>.symm)); have hp: cost0 A B 1=1:=by unfold cost0 Celeste.cost tickets; rw [Pi.one_apply,map_one,Celeste.lever.stockI hw (mul_eq_one_comm.mp hw)]; -- scope Sector.One ambiguity
    rw [hp]; refine ⟨Sector.one,?_⟩; unfold psiL; rw [star_one,act_one,(tickB _).2,Nat.cast_zero,zero_mul,zero_add]; exact (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) he)) -- tune
 | @both i j' S T x y g h K X₀ Y₀=>
    obtain ⟨A,B,ϕ,η,p0⟩:=X₀; obtain ⟨D,D',y',x',p1⟩:=Y₀; refine ⟨A∪D,B∪D',?_,?_,fun V W r e=>?_⟩
    · exact (card_union_le ..).trans ((Nat.add_le_add ϕ y').trans (le_of_eq (by ring)))
    · exact (card_union_le ..).trans ((Nat.add_le_add η x').trans (le_of_eq (by ring)))
    obtain ⟨i',v'⟩:= p0 V W (Subset.trans subset_union_left r) (Subset.trans subset_union_left e); obtain ⟨j₀,v''⟩:=p1 V W (Subset.trans subset_union_right r) (Subset.trans subset_union_right e); let X':=cost0 V W x; let V':=cost0 V W y
    have h:cost0 V W (x*y)=X'*V':=by unfold X' V' cost0 Celeste.cost tickets; have hw:= Pall.mun (K0.buildL (S:=V) (monograph _|>.symm)) (K0.buildZ (T:=W) (monograph _|>.symm)); rw [Pi.mul_apply,map_mul,Celeste.lever.mult hw (mul_eq_one_comm.mp hw)]
    have b:Y (S∪T)=Y S+Y T:=by unfold Y Post.blight; rw [inter_union_distrib_left, card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right (Finset.disjoint_of_subset_right inter_subset_right K)),Nat.cast_add]
    intro D₀; change Fock.Sector _ false (cost0 V W (x*y))∧ psiL (cost0 V W (x*y)) ≤ Real.exp (_*v+ Y (S∪T)*G); rw [h]; refine ⟨Sector.mul (?_ :Fock.Sector _ false X') (?_ :Fock.Sector _ false V'),?_⟩
    · exact Cin.widen (modes_monotone subset_union_left) i'
    · exact Cin.widen (modes_monotone subset_union_right) j₀
    rw [pairF _ _ i' j₀ (modes_orth K)]; exact (mul_le_mul v' v'' (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add,Nat.cast_add, b]; unfold v; congr 1; unfold Y; ring)
 | @expand k₀ S T Xw u p t' =>
    obtain ⟨A,B,ℓ,Y₀,q⟩:= t'; refine ⟨A,B,ℓ,Y₀,fun V W h i=>?_⟩; obtain ⟨u,v'⟩:= q V W h i; refine ⟨Cin.widen (modes_monotone p) u,?_⟩; exact v'.trans (Real.exp_monotone (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (Finset.inter_subset_inter_left p))) he))) -- tune
end Flush
end Alts
end YM.SU5.FiniteGaugeData.Cuprite.Spirit

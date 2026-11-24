import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Fume
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(S_α:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (TX: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
-- slotwise description of table variations including same orientation. no inequality used on Tensor powers.
variable (j:I)
variable (V W:I→ Torches n) -- V collision. fix
variable (u:ℂ)
def panelΩ (A:Torches n)(o:Seat n)(S:Hubber n):Paper n:= mintP A o S
lemma migration_F (F F':Torches n)(v:ℂ) (o:Seat n): mintP (v • F) o S=v • mintP F o S∧ mintP (F+F') o S=mintP F o S+mintP F' o S:=by
 have hp(Q V:Paper n)(i:Hubber n)(H:Hubber n): useS (Q+V) H i=useS Q H i + useS V H i∧ useS (v • Q) H i=v • useS Q H i:=by unfold useS; split <;> simp -- if_false etc
 constructor
 · unfold mintP; rw [show (v • F).1 = v • F.1 from rfl,(hp _ F'.1 _ _).2]; simp_rw [Prod.smul_snd, Pi.smul_apply, fun i=> (hp (F.2 i) F'.1 S i).2, smul_add, Finset.smul_sum]
 unfold mintP; rw [show (F+F').1=F.1+ F'.1 from rfl, (hp ..).1]; simp_rw [Prod.snd_add,Pi.add_apply,fun i=> (show useS (F.2 i+F'.2 i) i S=useS (F.2 i) i S+useS (F'.2 i) i S from (hp ..).1),sum_add_distrib]; abel -- tune
variable (P':I→ Boke n I)(N':I→ Boke n I)(K T: List I)
-- only need up to sublist.K parents same; if order changes can always use Curiosity. budgets variable
variable (Wv:I→ Torches n)(GΛ:I→ Torches n)
variable (ζμ:ℂ)
variable (dA:∀ i∈ T,∃ f g h c v,Bouquet I i P f g h v (V i) σ (M i) c) (dB:∀ i∈T, ∃ f g h c v,Bouquet I i P f g h v (Wv i) σ (P' i) c)(dC:∀i∈T,∃ f g h c v,Bouquet I i P f g h v (GΛ i) σ (N' i) c)
variable (gK:K.Nodup)(tK:T⊆K)(hT:ψS σ T)(p0:stampK M K)(p1:stampK P' K)(p2:stampK N' K)(h0:j∈ T)(h2:GΛ j=u • V j+ ζμ • Wv j)(h3:∀ i∈T,i≠j → Wv i=V i∧ GΛ i=V i)
local notation "D_A" M:max => disks I S A (Keeps F r M K)
local notation "H*"=> cryH F S (0:Key I) A
local notation "ΘB" G:max=>artΨ0 I S A H* G
local notation "M0" q:max =>ΘB (M q)
local notation "M1" q:max =>ΘB (P' q)
local notation "M2" q:max =>ΘB (N' q)
open NormedSpace
include dA dB dC gK tK hT p0 p1 p2 h0 h2 h3 v -- v collision
lemma dataL : tipI (D_A N') T=u • tipI (D_A M) T+ ζμ • tipI (D_A P') T:=by
 have hp(i:I)(F:Boke n I)(V:Torches n)(u:∃ f g h c v,Bouquet I i P f g h v V σ F c): ΘB F= binW (Icycle H*) (harpZ (αLines (mintP V (σ i) S) A)):=by obtain ⟨a,b,h,c,v,w⟩:=u; unfold artΨ0; rw [Bloom_M I S A i P a b h v V σ F w]
 have hv:M2 j=u • M0 j+ζμ • M1 j:=by
    rw [hp j _ _ (dC j h0),hp j _ _ (dA j h0),hp j _ _ (dB j h0), h2, (migration_F S (u • V j) (ζμ • Wv j) 0 (σ j)).2, (migration_F S (V j) 0 u (σ j)).1, (migration_F S (Wv j) 0 ζμ (σ j)).1]
    rw [show αLines _ A=u • αLines (mintP (V j) (σ j) S) A+ζμ • αLines (mintP (Wv j) (σ j) S) A from rfl]; simp_rw [map_add,map_smul]
 have he(i)(u:i∈T)(e:i≠j): M1 i=M0 i∧ M2 i=M0 i:=by
    rw [hp i _ _ (dA i u),hp i _ _ (dB i u),hp i _ _ (dC i u),(h3 i u e).1,(h3 i u e).2]; exact ⟨rfl,rfl⟩
 have hQ(s:List I)(f:s⊆ T)(h:j∉ s): (s.map (fun i=> M1 i)).prod=(s.map (fun i=> M0 i)).prod ∧ (s.map (fun i=> M2 i)).prod=(s.map (fun i=> M0 i)).prod:=by
    have hk(i)(u:i∈s):= he i (f u) (fun p=>h (p ▸ u)); exact ⟨congrArg List.prod (List.map_congr_left fun i t=>(hk i t).1), congrArg List.prod (List.map_congr_left fun i t=>(hk i t).2)⟩
 have hx(s:List I)(f:s⊆ T)(h:j∈s)(t:s.Nodup): (s.map (fun i=>M2 i)).prod=u • (s.map (fun i=>M0 i)).prod+ζμ • (s.map (fun i=>M1 i)).prod:=by
    induction s with
    | nil=> simp at h
    | cons i S ih=>
       simp_rw [List.map_cons,List.prod_cons]; obtain ⟨a,s⟩:= List.nodup_cons.mp t; let hr: S⊆T:=fun _ p=> f (List.mem_cons_of_mem _ p)
       by_cases q:i=j
       · subst i; obtain ⟨g,f⟩:= hQ _ hr a; rw [g,f,hv,add_mul, smul_mul_assoc,smul_mul_assoc]
       obtain ⟨g,h'⟩:= he i (f List.mem_cons_self) q; rw [ih hr (by simpa [Ne.symm q] using h) s,h', g,mul_add,mul_smul_comm,mul_smul_comm]
 have hb :PlateC j u ζμ T (tipI (exp∘(D_A M))) (tipI (exp∘(D_A P'))) (tipI (exp∘(D_A N'))):=by
    have hyp(q:List I)(h:q.Sublist T)(L:I→Boke n I)(p:stampK L K): VogueΓ (tipI (exp∘(D_A L)) q)=acts (((skimT I K q).map (fun i=> ΘB (L i))).prod) _:= Memo I σ S A L F r v K gK p q (List.Subset.trans h.subset tK) ((h.map σ).nodup hT) -- implicit w.W
    have hk(q:List I)(h:q.Sublist T): skimT I K q⊆ T :=fun i p=> h.subset (of_decide_eq_true (List.mem_filter.mp p).2)
    constructor
    · intro i p h; have hp:j∈skimT I K i:= List.mem_filter.mpr ⟨tK h0,decide_eq_true h⟩; apply vogue_inj; rw [map_add VogueΓ, map_smul, map_smul, hyp i p _ p2, hx (skimT I K i) (hk i p) hp (gK.filter _), act_add, act_smul, act_smul, hyp i p M p0,hyp i p P' p1]
    intro i p h; obtain ⟨J,J'⟩:=hQ (skimT I K i) (hk i p) (fun u=>h (of_decide_eq_true ((List.mem_filter.mp u).2))); exact ⟨vogue_inj ((hyp i p N' p2).trans ((by rw [J',←hyp i p M p0]))),vogue_inj ((hyp i p _ p1).trans (by rw [J,←hyp i p M p0]))⟩
 exact (linear_path (Seat n) σ _ _ (γRise_P ..) (γRise_P ..) T _ hT (γRise_P ..) j u ζμ hb (disk_Z _ _ _ _ _ _ v _ p0) (disk_Z _ _ _ _ _ _ v _ p1) (disk_Z _ _ _ _ _ _ v _ p2)).pos _ (List.Sublist.refl _) h0 -- tune arguments.
#print axioms dataL
local notation "τv" U:max G:max=> entryS σ L P (Keeps F r U K) T.toFinset G
lemma hue_data : cacheS I σ T.toFinset S (Keeps F r N' K) A = u • cacheS I σ T.toFinset S (Keeps F r M K) A+ ζμ • cacheS I σ T.toFinset S (Keeps F r P' K) A:=by
 apply sub_eq_zero.mp; apply cache_H S (fun S=>cacheS I σ T.toFinset S (Keeps F r N' K) A-(u • cacheS I σ T.toFinset S (Keeps F r M K) A+ ζμ • cacheS I σ T.toFinset S (Keeps F r P' K) A)) -- tune lambda input
 intro Z t; have hx:=dataL I σ A M F r v Z P j V u P' N' K T Wv GΛ ζμ dA dB dC gK tK hT p0 p1 p2 h0 h2 h3 -- order see #check
 rw [Finset.sum_sub_distrib,sum_add_distrib, ← Finset.smul_sum,← Finset.smul_sum]; apply sub_eq_zero.mpr; simp_rw [show ∀ L₀:Boke n I, ∑ X∈Z.powerset,cacheS I σ T.toFinset X L₀ A =tipI (disks I Z A L₀) T from fun X=> Eq.symm (Disk_version I σ Z A X T hT)]; exact hx
variable (hD:darkH F)
include hD
lemma Entrance_μ : τv N' x= u • τv M x+ζμ • τv P' x :=by
 funext A
 change (τv N' x) A=u • (τv M x) A +ζμ • (τv P' x) A
 simp_rw [sum_stamp,Finset.sum_apply,Finset.smul_sum,←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun S _=>?_; change (if _ then _ else _ : InkD n) A = _
 have hx:=hue_data I σ A M F r v S P j V u P' N' K T Wv GΛ ζμ dA dB dC gK tK hT p0 p1 p2 h0 h2 h3
 by_cases w:T.toFinset.card=1; swap; · simp only [if_neg w,Pi.smul_apply,hx,smul_add]; apply congrArg₂ (·+·) (smul_comm ..) (smul_comm ..)
 simp only [if_pos w,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,hx];
 let Rrr(M:I→Boke n I):=cacheS I σ T.toFinset S (foli (Keeps F r M K)) A
 have hd:T.toFinset={j}:=by obtain ⟨x,p⟩:=Finset.card_eq_one.mp w; rw [p]; have ht:j∈ ({x}:Finset I):= p ▸ List.mem_toFinset.mpr h0; rw [mem_singleton.mp ht]
 have hm(M:I→ Boke n I)(H: I→ Torches n)(d:stampK M K)(v':∃ f g h c v,Bouquet I j P f g h v (H j) σ (M j) c): Rrr M= if Pach (σ j)=S then AlphaY (H j).1 A else 0:=by
    obtain ⟨f,g,h,c,v',z⟩:= v'; unfold Rrr; rw [hd, Ink_sageY I σ M F r S j v hD K gK d (tK h0), bonO I σ S M P f g h v' c H j z]; split <;> rfl -- namespace bonO
 have hr:Rrr N'=u • Rrr M+ζμ • Rrr P':=by rw [hm _ _ p2 (dC j h0),hm _ _ p0 (dA j h0),hm _ _ p1 (dB j h0), h2]; split; exact congrFun ((Alpha_add _ _).trans (congrArg₂ _ (Alpha_s ..) (Alpha_s ..))) A; simp
 rw [show cacheS _ _ _ _ _ _= _ from hr] -- tune transparency
 simp only [Rrr,smul_add,smul_sub, ←sub_add_sub_comm]; simp_rw [show ∀ (x:ℝ)(y:ℂ)(D:Cipher n),x • y • D=y • x • D from fun _ _ _=>smul_comm ..]; abel
#print axioms Entrance_μ
end MintB
end MastTin
end YM.CF.XGarden
end

import GaugeFieldConstruction.Trimbo4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
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
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n: Side}
variable (v:I↪ J)
section
open Pressure Py Dial Oath TableF Lenten Layout Py.Riant Nor Py.Rate.Pitching.Focus
variable {m C L:Side}{e:ℝ}{j:ℕ}{hd:Odd L.val}{Y:Pricing j L hd (Thread j)}(U:Grasp Y C e)(K₀:Loom (mid m C))(X:GramM (mid m C))
variable (σ:J→ Seat (mid m C))(F:XE J (InkD (mid m C)) (mid m C))(K:KK J (Copy (mid m C)) (mid m C))(A:Rio J (mid m C))
lemma Ghost4 (t:Orbit (mid m C))(l:List I) : tipI (fun z=> denZ (Gram4 X (σ ∘ v) (squeezeD v (RX F A)) (squeezeD v (BX K A)) 0 z) U K₀ t) l= tipI (fun z=>denZ (Gram4 X σ F K A z) U K₀ t) (l.map v):=by
 apply Tipμ; intro i; apply congrArg (fun G=> denZ G U K₀ t); unfold Gram4 ΓNow ΦNow; have h: RX (squeezeD v (RX F A)) 0=squeezeD v (RX F A):=by change _+(0+0)=_; rw[add_zero,add_zero]
 have ht:BX (squeezeD v (BX K A)) 0=squeezeD v (BX K A):=by change _+0=_; rw[add_zero]
 rw [h,ht,shock,shock]
-- mask Journal.OK
variable (a b r h:ℝ)(t:0<h)(k:ℕ)(q:Horn4 σ F K X.p h t r a b k)(p:0 ≤r)
include q p
lemma carry4 : Horn4 (σ ∘ v) (squeezeD v F) (squeezeD v K) X.p h t r a b k:= ⟨sawP _ _ _ _ q.core,sawP _ _ _ _ q.holdK,sight_r _ _ _ q.paw p, sight_r _ _ _ q.crowd p, fun i h=> q.haloT (i.1.image v,i.2) h⟩
lemma shiftJournal (f:∀ i,F (∅,i)=0): Journal1 X.p t σ (fun i j=>F (i,j)) (Lapse (fun i j=> K (i,j))) a r b:=by
 obtain ⟨T,Y⟩:= lapKD t p (fun i j=>K (i,j)) q.crowd q.holdK; exact ⟨q.paw,T, q.core,Y, funext f,if_pos rfl⟩
omit p q
-- hull clock.Count. accepts all rosters simultaneously; applies also if vac terrain. TF enforcing cost Chron
variable (P:RG.Patch) (O M:ℝ)(m₀ :ℕ)
-- installation predicate
structure Chart4 (x:ℝ):Prop where
    bottom:16≤radiusB x
    boot: Boot4 (radiusB x) (Speedy (fun x=> olderM P x O) (ounce4 ∘ radiusB) k x) (Eta4 k (radiusB x)) (ounce4 (radiusB x)) (olderM P x O) (Flow4 k (radiusB x))
    white: booty4 3 (radiusB x) (WhiteC (ounce4 ∘ radiusB) k x+ GrayC (fun x=>olderM P x O) (ounce4 ∘ radiusB) k x) ≤ M*QLife P x
    forceC: booty4 2 (radiusB x) (GrayC (fun x=>olderM P x O) (ounce4 ∘ radiusB) k x) ≤ M * QLife P x
lemma chart4_g(o:0<O)(m:0<M):∀ᶠ x in atTop, Chart4 k P O M x:=by
 filter_upwards [Age4γ P O k o M M m m,YM.Work.E01.radiusB_tendsto.eventually_ge_atTop 16] with i h w; exact ⟨w,h.1,h.2.1,h.2.2⟩ -- qualify
variable (p₀:X.p.power=2)(p₁:X.p.order=6)
include U K₀ p₀ p₁
lemma Epoch4 (x:ℝ)(g:Chart4 k P O M x)(hb:X.p.B=radiusB x)(w:Horn4 σ F K X.p h t 1 (21/16) (O*QLife P x) m₀)(μ:J→ℝ)(L₀:List J)(s:J→ List J)(θ:J→Seat (mid m C))(f:Things σ F K s (fun i=>Grap (σ i) (θ i)) L₀)(d:supplyL k σ L₀)(b:∀ i∈L₀, ∃ y:ℝ,(X.p.B:ℝ)^3 ≤ y∧ (separation (σ i) (θ i):ℝ) ≤ y ∧ 0≤μ i ∧ μ i ≤ Real.exp (-y))(l:∀ i∈L₀,separation (σ i) (θ i)> L.val * (4*X.p.B+2) +2*X.p.B): let Ξ:= ProgramL σ F K μ s (fun i=> Grap (σ i) (θ i)) L₀; Horn4 (σ ∘ v) (squeezeD v (RX F Ξ)) (squeezeD v (BX K Ξ)) X.p h t 1 (5/4) ((O+M)*QLife P x) m₀ ∧ (∀ i:I,v i ∈ L₀→ Cresc L.val (KeyUp X.p) (Zhub (σ (v i))) →∀ j:ℕ, TollsK X.p (σ (v i)) X.J.M (fun y=> squeezeD v (RX F Ξ) ({i},y)) L (QLife P x) h M j 0)∧∀ t':Orbit (mid m C),Rue.FleetS X.p.threshold t'.1 →∀ (l':List I)(T:List J)(d':ℂ), Vote σ μ s L₀ (l'.map v) T d'→ tipI (fun z=> denZ (Gram4 X (σ∘v) (squeezeD v (RX F Ξ)) (squeezeD v (BX K Ξ)) 0 z) U K₀ t') l'= d' • tipI (fun z=>denZ (Gram4 X σ F K 0 z) U K₀ t') T:=by
 intro Ξ; let G:= fun i:J=> Grap (σ i) (θ i)
 have e: FlushL σ μ G (ounce4 X.p.B) (5/4) X.p.B L₀:=by
    refine ⟨fun i _=>rfl,fun i p=>?_,fun i p=>(b i p).choose_spec.2.2.1⟩
    obtain ⟨V,y,p,q,s⟩:=b i p; exact opening X.p.B (σ i) (θ i) _ _ _ (hb ▸ g.bottom) y p s (by norm_num) (by norm_num[ζd])
 obtain ⟨u,v',q⟩:= Calculation4 U K₀ X P σ F K h t m₀ k μ θ s O M L₀ x (by simpa [hb] using g.boot) w f d e p₀ p₁ hb g.white g.forceC
 refine ⟨carry4 v _ _ _ _ _ _ _ _ t _ v' zero_le_one, fun i q h' j=>?_, fun a b l T d e=>?_⟩
 · rw [show (fun y:Scree.Hub _=> squeezeD v (RX F Ξ) ({i},y))=(fun y=>RX F Ξ ({v i},y)) from (funext fun i=>by simp[squeezeD])]
   refine output4_core σ F K _ μ s G t M _ j _ _ u (fun _ _=>rfl) ?_ X.J.M (v i) q (f.face _ q) h'
   intro i p; let D:= (G i).val.2; let b:=X.p.B; have H:separation (σ i) (θ i) ≤ coverNumber b D * (4*b+2) +2*b:= extent D b (G i).property (mem_insert_of_mem (mem_singleton_self _)) -- tune args
   have hv:= l i p; let Y:=coverNumber b D; have he:L.val< Y:=by by_contra g; push Not at g; exact hv.not_ge (H.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ g) _))
   exact he.le.trans (Nat.le_self_pow (by norm_num) _) -- tune args
 exact (Ghost4 v U K₀ X σ F K Ξ a l).trans (q a b (l.map v) T d e) -- underscore parse.
#print axioms Epoch4
end
end Iona
end YM.CF.Scree.Ing
end

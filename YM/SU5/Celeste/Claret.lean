import YM.SU5.Celeste.Savory
import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake
/-! # One-repast estimate on the chosen course. Includes raw power bill. -/

set_option autoImplicit false
set_option maxHeartbeats 225000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
lemma revive(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
open YM.CF.Lamour.Bridge.Celeste Sonnet
open YM.CF.Lamour.Bridge
variable {N:Side}{j r d p:ℕ}{B σ u θ C ε ξ:ℝ}{M: Tulip.Male}
lemma striking (L:List (Sonnet N)): buffet L=cartMark univ (Sonnet.x ∘ L.get):= by
 funext X; let f := fun i: Fin L.length=> (L.get i).x X; let g:= fun a:Sonnet N=> a.x X;
 have he {W:List (Sonnet N)}: buffet W X= (W.map g).prod:=by induction W with| nil=> exact congr_fun buffet_empty X|cons i K ih=>rw [buffet_more,List.map_cons,List.prod_cons, Pi.mul_apply,ih] -- tune
 rw [he]; unfold cartMark; change _=((Finset.univ.sort fun i j:Fin L.length=>i ≤ j).map f).prod; rw [Fin.sort_univ, ←List.ofFn_eq_map]; have ht:f=g∘ L.get:=rfl; rw [ht,←List.map_ofFn,List.ofFn_get]
lemma buffet_price (pL:0≤C) {L:List (Sonnet N)}(t:Sylvan j r d p M ε ξ C σ L) (X:Fields N) : ‖buffet L X‖≤C^L.length:=by induction L with
 | nil=> simp [buffet]; -- tune
 | cons i L ih=> rw [buffet_more, Pi.mul_apply,List.length_cons,pow_succ']; refine (norm_mul_le ..).trans (mul_le_mul ((t.core _ List.mem_cons_self).boxed.1 X) (ih (show Sylvan j r d p M ε ξ C σ L from ⟨fun k v=>t.core _ (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp t.annex).2⟩)) (norm_nonneg _) pL)
lemma many_price (v:0≤C)(b:ℕ) (g:Meringue.{0} Y p r (180*d) ε ξ C σ θ)(u:0<σ)(c:0≤θ)(z:θ*(4*((b:ℝ)+(addgap (tent Y H):ℝ)))^4 ≤1) :
 ∀ᶠ s in atTop,∀ᶠ i in atTop, ∀ᶠ k in atTop,∀ (A:Sonnet (Papal.count Y s i)), A.Cost P.K.j r d (gram Y s i k).J.M ε ξ C σ → (∀ i,cows i (Lattice.halo p A.S) b) → ‖Journey.compass Y i k s A.x‖≤4*Real.exp 1*σ:=by
 obtain ⟨a,a'⟩:= Filter.eventually_atTop.1 (ownsHalo (j:=P.K.j) (P.kJ.symm ▸ (by decide : 1 ≤ (4:ℕ))))
 let K:= tent Y H; filter_upwards [g] with s g;
 filter_upwards [g,(count_grows Y s).eventually_ge_atTop (b+addgap K+a.val)] with i h gV;
 let N:= count Y s i; have ht:b+addgap K+a.val ≤ N.val:=gV; let S:=(More N).val^4; let G:=Real.exp 1*σ; let Φ:= max 1 C; let E:= min 1 G; let P₀:= Φ^S; have hG:0<G:=by unfold G; positivity
 have he:0<E:=lt_min zero_lt_one hG; have hΦ:1≤Φ:=le_max_left ..; have h₂:0<Φ:=zero_lt_one.trans_le hΦ; let x:= E^S/P₀; have hg:0<x:=by unfold x P₀; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y x hg s] with k X U A τ pL
 let F:=Journey.compass Y i k s; let D:= solder Y i k X.depth s; let m:=momentm Y i s; have hH:HaloTw P.K.j N:= a' _ (show a.val≤N.val from (by omega)) (Vale.val_e ..); let M:=(gram Y s i k).J.M
 obtain ⟨L,l,h₀,h₁,h₃,e⟩:= Sonnet.trefoil hH (revive Y H s i k X) (terrain Y H (Y.ir i) s).symm (show b+addgap K≤N.val from by omega) _ τ pL
 let W:= buffet L; let n:=L.length; let V(i':Fin n):=L.get i';
 have ht':θ * sites N ≤ n:=by
    let Z:= 4*(b+addgap K);
    have hp:θ * ↑(Z^4) ≤ 1:=by exact_mod_cast z -- casts tune
    have hl:sites N ≤ ↑(n*Z^4):=by unfold sites; exact_mod_cast h₃
    have hg:=mul_le_mul_of_nonneg_left hl c; have hx:=mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) n); push_cast at hg hx; linarith
 have H1: ‖F W‖≤ G^L.length:=by
    refine (broken_ratio Y i s k W).trans ?_; unfold W; rw [striking L]; apply le_trans (h k X.depth X.enters (Fin n) _ _ (Sonnet.S∘ V) (Sonnet.o ∘ V) ?_ ?_) -- tune
    · unfold G; rw [mul_pow,←Real.exp_nat_mul,show σ^L.length=Real.exp ((n:ℝ)*Real.log σ) from (by rw [Real.exp_nat_mul,Real.exp_log u]), ←Real.exp_add]; rw [mul_one,Finset.card_univ,Fintype.card_fin]; exact Real.exp_le_exp_of_le (add_le_add ht' (le_refl _))
    · intro i v; exact (l.core (V i) (List.get_mem L i)).issued hH.1 -- get
    · intro i _ j _ u; rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne u) with t|t; exact l.annex.rel_get_of_lt (show i < j from t); exact Distant.symm (l.annex.rel_get_of_lt (show j < i from t))

 -- move before
 change L.length ≤ S at h₁; change ‖D _‖^ L.length ≤ ‖D W‖ at e;
 have He : (2:ℝ)≤2^L.length:= by simpa only [pow_one] using (pow_le_pow_right₀ (a:= (2:ℝ)) (by norm_num) (show 1 ≤ L.length from h₀)) -- tune
 have HC: ‖F W-D W‖≤G^L.length:=by apply (U i X.depth W P₀ l.occupy.env (fun y=>(buffet_price v l y).trans ((pow_le_pow_left₀ v (le_max_right ..) _).trans (pow_le_pow_right₀ hΦ h₁)))).trans; unfold x P₀; rw [div_mul_cancel₀ _ (pow_pos h₂ _).ne']; exact (pow_le_pow_of_le_one he.le (min_le_left ..) h₁).trans (pow_le_pow_left₀ he.le (min_le_right ..) _)
 have HH: ‖D A.x‖ ≤2*G:= by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) h₀.ne').mp; apply le_trans e; rw [mul_pow]
    have hl:=norm_le_norm_sub_add (D W) (F W); rw [norm_sub_rev] at hl; refine (hl.trans (add_le_add HC H1)).trans ?_; rw [← two_mul]; gcongr
 have H₂:‖F A.x-D A.x‖≤G:=by apply (U i X.depth A.x P₀ τ.owner.env (fun y=>(τ.boxed.1 y).trans ((le_max_right ..).trans (show Φ≤ Φ^S from by simpa only [pow_one] using (pow_le_pow_right₀ hΦ (show 1 ≤ S from (lt_of_lt_of_le h₀ h₁))))))).trans; unfold x P₀; rw [div_mul_cancel₀ _ (pow_pos h₂ _).ne']; apply le_trans (pow_le_pow_of_le_one he.le (min_le_left ..) (show 1 ≤ S from h₁.trans' h₀)); rw [pow_one]; exact min_le_right ..
 change ‖F A.x‖≤_; apply (norm_le_norm_sub_add (F A.x) (D A.x)).trans ((add_le_add H₂ HH).trans ?_); unfold G at *; nlinarith only [hG]
lemma from_block {w:Axis}(A:Sonnet N)(h:A.Cost j r d M ε ξ C σ): cows w (Lattice.halo p A.S) (2*(r+p)):=by
 obtain ⟨t,g⟩:=blocks_rest A.o (r+p) w; exact ⟨t,fun y x=>g _ (Lamour.Bridge.fit h.tight x) ⟩
lemma count_la (s:ℕ): Tendsto (fun i=>count Y s i) atTop atTop:=tendsto_atTop.2 fun p: Side=> (count_grows Y s).eventually_ge_atTop p.val
abbrev Weaver:= (N:Side)→ Mark N
def household (K:Calibration)(F:Weaver): Buffered.Family K:=fun m=>F (K.c m)
/-- Budget available after choosing altitude & allowed shape of W. For any `r`: need per-site κ ≤ .. . -/
abbrev BuyW (K:Calibration)(k r:ℕ)(t:ℝ):= t*(4*((↑(2*(r+k)):ℝ)+↑(addgap K)))^4≤1
abbrev BroadWeld (N:Side)(F:Weaver)(r d:ℕ)(j:ℕ)(ε ξ C B:ℝ):Prop := ∀ M:Tulip.Male,∃ S o, Sonnet.Cost j r d M ε ξ C B (Sonnet.mk (N:=N) (F N) S o)
theorem continuum_w (v:0≤C) (g:Meringue.{0} Y p r (180*d) ε ξ C σ θ)(u:0<σ)(c:0≤θ)(z:BuyW (tent Y H) p r θ)
 {J K:ℕ→ℕ}{I E} (X:Universal Y H J K I E):∀ᶠ s in atTop,∀ F:Weaver, TestFamily (tent Y H) true (household (tent Y H) F) → (∀ᶠ N:Side in atTop,Even N.val → BroadWeld N F r d P.K.j ε ξ C σ) → ‖E s (household (tent Y H) F)‖ ≤ 4*Real.exp 1*σ :=by
 filter_upwards [many_price Y H v _ g u c z] with s pX F h q; let W:= tent Y H; let A:= household W F; have hk:=X.together s A h; apply le_of_tendsto hk.periods.norm; refine X.pick.grow_i.tendsto_atTop.eventually (p:=fun i=> ‖I s A i‖≤_) ?_; filter_upwards [pX,(count_la Y s).eventually q] with i gρ pρ; let Ns:= count Y s i; apply le_of_tendsto (hk.inner i).norm; refine X.pick.grow_k.tendsto_atTop.eventually (p:=fun k=> ‖Journey.sharp Y H s i k A‖≤_) ?_; filter_upwards [gρ] with k gk; obtain ⟨S,o,hS⟩:=pρ (Vale.val_e ..) (gram Y s i k).J.M; let y:=gk _ hS (fun _=> from_block _ hS); change ‖Journey.compass Y i k s (send Y H i s _)‖≤_; apply y.trans'; apply le_of_eq; congr 2; exact resideA F _ Ns (terrain Y H (Y.ir i) s) -- tune
where resideA(F:Weaver)(A B:Side)(g:A=B): (g ▸ F A)=F B:=by subst B; rfl
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.many_price
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.continuum_w

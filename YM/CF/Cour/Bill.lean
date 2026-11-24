import YM.CF.Cour.Coin
import YM.CF.Proa.Uta
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{N m X B L:Side}{n k j:ℕ}{e d t x u C A P:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}
lemma ampleB{x:Nom (CSide m B) (CSide X B)}(s:JointB G x e)(t:e ≤ d):JointB G x d:= ⟨s.fg.shrink t,s.cg.shrink t,fun i=> (s.follow i).trans t⟩
-- label transfer incl matrix elements
lemma tauE(n:ℕ)(p:0≤P)(pe:0<d):∃ C:ℝ,1≤ C∧∀ {m X B:Side}{e:ℝ}(G:Ratio (CSide m B) (CSide X B)),0<e →e≤d → ∀ A: Coil (CSide m B) (CSide X B)→ Op (Iota G), ∀ b:Bool, ∀ a w:ℝ,0<a →Crown (badge _) (Peaks.parcel G b d) (Peaks.parcel G b d) a w (fun x=> A x.val) → Screen (dressL G e) (LineE n G P e) n (fun i=> Matrix.trace (A (unionP i.val))) (a/2) (C*quartzK a w):=by
 obtain ⟨C,T,H⟩:= profile_X n P p
 let t:ℝ:=(1+2^n/d)^n; let V:=max 1 (composeCost n t C)
 refine ⟨V,le_max_left ..,fun {m X B e} G h hz A b a w q hp=>?_⟩
 let f(x:Rent0 G e):↑(legal G d):= ⟨_,ambient _ _ h hz x.property⟩
 have hf:Continuous f:=by unfold f; exact (((profile_c.comp (continuous_fst.comp continuous_subtype_val)).prodMk (profile_c.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _) -- tune
 obtain ⟨F,D,q',W,r⟩:=hp; let Q(S)(x):=(F S (f x)).trace
 have hp:0≤V:=le_max_of_le_left zero_le_one
 refine ⟨Q,fun S=>V*ledgerV (D S),fun S=>?_,fun i=> ?_,fun i=> Eq.trans (congrArg Matrix.trace (r (f i))) (Matrix.trace_sum ..)⟩
 · have he:= ledgerT (q' S).toTicket; refine ⟨⟨mul_nonneg hp he.posT,fun p=>he.conduct (right_ne_zero_of_mul p), he.continuousE.comp hf,fun x=> (he.norms (f x)).trans (le_mul_of_one_le_left he.posT (le_max_left ..)),fun x y p=>?_,fun x g=>?_⟩,?_⟩
   · have hv:= he.varies (f x) (f y); rw [show (tempo G d).eval S (f x) (f y)=0 from ?_,mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
     change deal _ _ (unionP _) (unionP _) / _=0; unfold deal unionP; have hu{n:Side}(S:Seal (Site (More n)))(X Y:Bkg (More n))(h: Agrees S X Y):fare S (profile X) (profile Y)=0:=by
          unfold fare; apply sum_eq_zero; intro i hy; rw [show profile X i=profile Y i from funext fun z=>by unfold profile; rw [h i (mem_filter.mp hy).2.1 (mem_filter.mp hy).2.2],sub_self,norm_zero]
     dsimp only; rw [hu _ _ _ p.1,hu _ _ _ p.2,add_zero,zero_div] -- tune
   · have hp: f ((dressL G e).dress g x) = (tempo G d).drive g (f x):= Subtype.ext (jig G g _); exact (congrArg (fun i=>Matrix.trace (F S i)) hp).trans (he.gauge g _)
   intro E _ _ _ U k g Q' x hx; let X(i:E):= (f (g i)).val; let Y:=Q' x hx
   have hy : Allows n X x C:= (H _ _ Y.1).pair (H _ _ Y.2)
   have hk : ball (X x) d⊆ legal G d:=fun r hr=>⟨(g x).val,ampleB (g x).property hz,mem_ball_iff_norm.mp hr⟩
   have ht i j : Allows n (fun x=> F S (f (g x)) i j) x (V*D S i j):=by
     let Φ:= fun x=> F S x i j; let c:=D S i j
     have hl:Allows n (equalizer Φ ∘ X) x (composeCost n (c*t) C):= (allows_looks (q' S|>.fuel i j) ((q' S).expo i j).connected hk pe n ((q' S).expo i j).bounded).comp (f:=X) hy
     apply (hl.mono ?_).germ _
     · calc
         composeCost n (c*t) C=composeCost n t C*c:=by unfold composeCost; ring
         _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) ((q' S).expo i j).positive
     filter_upwards [] with z; exact dif_pos (f (g z)).property
   let hA := allows_sum (f:=fun i x=> F S (f (g x)) i i) (s:=Finset.univ) (fun i _=>ht i i); apply hA.mono; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> single_le_sum (f:=fun j=>D S i j) (fun j _=>(q' S).nonn i j) (mem_univ i)) hp
 unfold hitE; simp_rw [mul_left_comm (Branch.rent ..) V,←mul_sum]; exact mul_le_mul_of_nonneg_left (Branch.tall (s:=Peaks.parcel G b d) (P:=F) (fun S=>(q' S).toTicket) W q (temper_cap ..) quota_p.le i) hp
open Pec
lemma helix (n:ℕ)(Z:ℝ)(hz:1 ≤Z)(o:Odd L.val)(hu:Even j)(hy:1≤j)(K:WG ι)(hk:Lively K)(ht:∀ i n,K i n 1=0)(M:ι→Male):∃ b c d:ℝ,0<b∧0<c∧0<d∧∃ N:ℕ,∀ e:ℝ,0<e→e≤d →∀ {m X B:Side}(G:Ratio (CSide m B) (CSide X B)),G.count=L→N≤ (CSide m B).val →∀ i, Screen (dressL G e) (LineE n G Z e) n (fun x=> invoice (Proa.nuke L o j K M i G (unionP x.val))) b c∧∀ x:Rent0 G e, ‖Proa.nuke L o j K M i G (unionP x.val)‖<1:=by
 obtain ⟨⟨d',h,dq,Q⟩,a,w,d,ha,hW,hd,l,H⟩:= pier_s L o j hu hy K hk ht M
 obtain ⟨C,c,H'⟩:=tauE n (zero_le_one.trans hz) hd
 refine ⟨a/2, max 1 (C*quartzK a w),min d d',half_pos ha,lt_max_of_lt_left one_pos,lt_min hd h,max dq l,fun e hf hx {m A B} G hy ht i=>?_⟩
 let X(x):=Proa.nuke L o j K M i G x; have hp (x:Rent0 G e): ‖X (unionP x.val)‖<1:= ((Q i G hy ((le_max_left ..).trans ht)) _ (ambient _ _ hf (hx.trans (min_le_right ..)) x.property)).trans_lt (by norm_num) -- tune
 have hh:= H' G hf (hx.trans (min_le_left ..)) (fun x=> pencil (X x)) true a w ha (H i G hy ((le_max_right ..).trans ht)); simp_rw [show ∀ i: Rent0 G e, Matrix.trace (pencil (X (unionP i.val))) = invoice (X (unionP i.val)) from fun i=> (tally_log (hp i)).symm] at hh
 exact ⟨hh.reserve le_rfl (le_max_right ..), hp⟩
end YM.CF.Cour

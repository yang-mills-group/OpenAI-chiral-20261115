import YM.CF.Pic.Ment
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a t x y T r:ℝ}{P:Grasp Y B e}
-- fortune.Rt epoch
lemma Ieq(H:Pearl P)(S:Stamped j L o Y)(p:1≤j)(g:0<e)(k:P.roundZ ≤ (CSide m B).val)(u:Pad j (CSide m B))(d:Candle)(F:Slide (CSide m B) d)(M:Jill.Male)(e:∀ i,Jill.cup (CSide m B) j M r (brimV F i)=disk j M (angle F i)): ‖AMP m P d M‖=iceK j F M r:=by rw [rich k g M u d F,iceK]; exact prod_congr rfl fun i _=> (e i).symm
local notation "pn"=> CSide m B
structure Span (H:Pearl P)(K b x C l r:ℝ)(n:ℕ) where
 p :1≤ j
 eP:0<e
 stmt: Stamped j L o Y
 pos:0<b
 less : 0<l
 cP:1≤C
 kP:0<K
 xP:0<x
 rP:0<r
 gap(N':Side)(d:Candle):∃ h:Hat,Medal N' (sun d h (More N')) l
 plan(m:Side)(u:n≤(CSide m B).val):P.roundZ ≤ (CSide m B).val ∧ Pad j (CSide m B)
 fits (m:Side)(u:n≤(CSide m B).val)(M:Jill.Male):iceK j (too (CSide m B)) M r=angel m P M
 powV(m:Side)(g:n≤(CSide m B).val)(M:Jill.Male)(d:Candle)(F:Slide (CSide m B) d):let c:=iceK j F M r; let x:=angel m P M;b*x≤c ∧ c≤C*x∧(Medal (CSide m B) d l→ ‖AMP m P d M‖=c) ∧ Yep (K*(CSide m B).val) (mateK (CSide m B)) (changeM (m:=m) P (Kea.tax d) M) (C*x)
 pale(m:Side)(u:n≤(CSide m B).val)(M:Jill.Male)(d:Candle)(p:slowT (Domain m B) d)(V:Bkg (Domain m B))(t:ℝ)(g:0<t)(w:t≤1)(h:(CSide m B).val^10*t≤x): lawnK V (Kea.tax d) t→ Guard V e∧Yep (K*(CSide m B).val) (mateK (CSide m B)) (changeM P V M-changeM P (Kea.tax d) M) (C*(CSide m B).val^10*t*angel m P M)
lemma sortV (h:1≤j)(r:ℝ):∃ n:ℕ,∀ N:Side,Even N.val→ n ≤ N.val→Pad j N ∧ r*pinch N^2≤ 1/8 ∧ 18*pinch N< Next.Free.zone:=by
 obtain ⟨t,T⟩:=gave j h; have hf:Tendsto (fun n:ℕ=>Real.pi/(n:ℝ)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
 obtain ⟨N,Q⟩:= eventually_atTop.mp (Eventually.and (show ∀ᶠ i:ℕ in atTop,r*(Real.pi/i)^2 ≤ 1/8 from ((hf.pow 2|>.const_mul r).eventually (ge_mem_nhds (by norm_num)))) (show ∀ᶠ i:ℕ in atTop,18*(Real.pi/i)<Next.Free.zone from (hf.const_mul 18).eventually (gt_mem_nhds (by simpa using Next.Free.zone_pos))))
 exact ⟨N+t,fun m p h=>⟨T _ p (by omega),Q m.val (by omega)⟩⟩
lemma crop0 (H:Pearl P)(S:Stamped j L o Y)(p:1≤j)(g:0<e):∃ K b x C l r:ℝ,∃ n:ℕ, Nonempty (Span H K b x C l r n):=by
 obtain ⟨l,hL,l',Lp⟩:=Sods.clears; obtain ⟨r,h,Hr⟩:= zipper p hL; obtain ⟨d,C,d',C',X⟩:= pole p h; obtain ⟨G,T,hG,hT,D⟩:= Flare.tuneup p h; obtain ⟨z,v,l0,m',n,Q⟩:= skin_bounds S H p g hT.le; obtain ⟨N,k⟩:= sortV p r
 let c:=1+C+G*C+v*(G*C); have hc: 1≤c:=by unfold c; nlinarith [mul_pos m' (mul_pos hG C')]
 let u:=n+N+P.roundZ; have ht(m:Side)(e:u ≤ (CSide m B).val): P.roundZ ≤ (CSide m B).val:=by unfold u at e; omega
 have hv(m:Side)(e:u ≤ (CSide m B).val):= k (CSide m B) (by change Even (m.val*2*B.val); exact Even.mul_right (even_two.mul_left _) _) (show N ≤(CSide m B).val from by unfold u at e; omega)
 have he(m:Side)(q:u ≤ (CSide m B).val)(M:Jill.Male) : ‖AMP m P emptyC M‖=iceK j (too (CSide m B)) M r:= Ieq H S p g (ht m q) (hv _ q).1 emptyC _ _ (Hr _ (hv _ q).1.1 _ _ M (empty_m l' _))
 have hh (m:Side)(q:u ≤(CSide m B).val)(M:Jill.Male)(b:Candle)(F:Slide (CSide m B) b): Yep (T*(CSide m B).val) (mateK _) (changeM (m:=m) P (Kea.tax b) M) (G*C*angel m P M):=by
    let N':=CSide m B; obtain ⟨t,h,l⟩:= hv _ q; have hp:= sea_g (ht m q) _ (tax_guard b _ _ g.le) M; rw [show spar j M _= _ from t.2 b F M] at hp -- shape
    have he':= (X N' t.1 l b F M).2; rw [← he _ q M] at he'; exact (Yep.weigh (show Yep (T*N'.val) _ _ _ from D _ t.1 h b F _ _ hp) (le_trans (mul_le_mul_of_nonneg_left he' hG.le) (le_of_eq (by change _=G*C*‖_‖; rw [mul_assoc]))) (by positivity))
 refine ⟨T,d,z,c,l,r,u,⟨⟨p,g,S,d',hL,hc,hT,l0,h,Lp,fun m q=>⟨ht m q,(hv m q).1⟩,fun m q M=>(he m q M).symm,?_,?_⟩⟩⟩
 · intro m q M b F C' x; obtain ⟨e0,eK,w⟩:= hv m q; obtain ⟨hx,l⟩:= X _ e0.1 w b F M; rw [←he m q M] at hx l; have hE:=angel_p H S (ht _ q) p g M e0
   refine ⟨hx,le_trans l (mul_le_mul_of_nonneg_right (show C ≤ c from by unfold c; nlinarith [mul_pos m' (mul_pos hG (show 0<C by assumption)),(show 0<G*C from mul_pos hG (by assumption))]) hE.le),fun t=>Ieq H S p g (ht _ q) e0 _ _ _ (Hr _ e0.1 _ _ _ t),(hh _ q M b F).weigh ?_ (by positivity)⟩; apply mul_le_mul_of_nonneg_right _ hE.le; unfold c; nlinarith [mul_pos m' (mul_pos hG (show 0<C by assumption))] -- tune shadow
 intro m p M b hb V y hy w e hp; obtain ⟨h',A,D,t⟩:= Q m (by unfold u at p; omega) M V b y hb hy w e hp
 have hA:=angel_p H S (ht _ p) (p:=‹1≤j›) g M (hv _ p).1; refine ⟨h',?_⟩; rw [← D]; refine (t.2 _ _ _ (by positivity) (hh _ p M b (skim _ b))).weigh ?_ (by positivity); calc
    _ = (v*(G*C))* (CSide m B).val^10*y*angel m P M:=by ring
    _ ≤ _:=by gcongr; unfold c; nlinarith
end YM.CF.Pic

import GaugeFieldConstruction.Farouche
set_option autoImplicit false
set_option maxHeartbeats 140000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
variable (t:ℝ)(z x y:Cover)(m:ℕ)
abbrev mount (t:ℝ)(x:Cover):= t • off x
-- combine contract list. all payouts independent orientations.AP masses actual use unchanged
abbrev BigP (x y:E4):= Wick.pair.compr₂ (eye (y-x))
def Lake (s:Cover):Chip→Book
| .litt a b=>αG (Gauke s a m t) (Gauke s b m t)
| .cuff a b=>αF (Freight s a false m t) (Freight s b true m t)
| .creel g a b=>αM (Gauke s g m t) (Freight s a false m t) (Freight s b true m t)
def Berth (x:Cover): Chip→ Prop
| .litt a b=>zG x a∈grabG ∧ zG x b∈ grabG
| .cuff a b=> zF x a∈ grabF ∧ zF x b∈grabF
| .creel g a b=>zG x g∈grabG∧ zF x a∈grabF∧ zF x b∈grabF
lemma Uptick (N:Side)(v:Genre)(i:ShapeZ N x v): Berth x (ChipUp N x v i):=by
 cases v with
 | gauge=> exact ⟨forkG _ _,forkG _ _⟩
 | pure=> exact ⟨forkF _,forkF _⟩
 | mixed=>exact ⟨forkG _ _,forkF _,forkF _⟩
abbrev RatesG (C:ℝ):Prop:=∀ i j:Wα,zG x i∈grabG→zG y j∈ grabG→ Rally C (t^(m+1)) (gT t i j) (eye (mount t y-mount t x) (ge (Gauke x i m t) (Gauke y j m t)))
abbrev RatesF (C:ℝ):Prop:=∀ i j:Wφ,zF x i∈grabF→ zF y j∈ grabF→ Rally C (t^(m+1)) (fT t i j) (eye (mount t y-mount t x) (yarn false (Freight x i false m t) (Freight y j true m t)))
def Captain (C:ℝ):Prop:= RatesG t x y m C∧RatesF t x y m C∧RatesF t y x m C
lemma extraK (v:0≤ t){C B:ℝ}(p:Captain t x y m C)(w:C≤B): Captain t x y m B:= ⟨fun i j r s=>(p.1 _ _ r s).mono w (by positivity),fun i j r s=>(p.2.1 _ _ r s).mono w (by positivity),fun i j r s=>(p.2.2 _ _ r s).mono w (by positivity)⟩
-- weight. exponents
abbrev Pval (C:ℝ):=2*C*C
abbrev Qval (C:ℝ):=2*Pval C*C
abbrev Zval (C:ℝ):=2*C*(Pval C+ Pval C)
abbrev cashF (C:ℝ):=32*C^4
lemma sizeK (C:ℝ)(h:1≤ C): let Z:=cashF C; Pval C+ Pval C≤ Z ∧ Pval C≤ Z ∧ Qval C ≤ Z ∧ Zval C+Zval C+ Zval C+Zval C≤ Z ∧ Qval C+Qval C ≤ Z ∧ 2*(Qval C+Qval C)*C≤ Z ∧ 2*Pval C*(Pval C+Pval C)≤ Z:=by
 intro Z; have hp:0 ≤ C:= zero_le_one.trans h; have he: C^1 ≤ C^2 := pow_le_pow_right₀ h (by decide); have hx: C^2≤ C^3:= pow_le_pow_right₀ h (by decide); have ht:C^3 ≤ C^4:=pow_le_pow_right₀ h (by decide)
 dsimp [Z,cashF,Zval,Pval,Qval]; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
lemma breech {C:ℝ}(p:Captain t x y m C)(h:1≤ C)(ht:0<t)(a b:Chip)(v:Berth x a)(s:Berth y b) : Rally (cashF C) (t^(m+1)) (Chip.budget2 (gT t) (fT t) a b) (paiB (mount t x) (mount t y) (Lake t m x a) (Lake t m y b)):=by
 have hu:= pow_nonneg ht.le (m+1); rcases (show _ from (sizeK C h)) with ⟨X,P,U,_,_,_,_⟩; have hz:Rally (cashF C) (t^(m+1)) 0 0:= Rally.zero _ _ (by unfold cashF; positivity) hu; rcases p with ⟨G,H,F⟩
 cases a with
 | litt i j=> cases b with
              | litt k l=>rw [Lake,Lake, ΨP]; exact ((((G i k v.1 s.1).threes (G j l v.2 s.2)).twice ((G i l v.1 s.2).threes (G j k v.2 s.1))).mono X hu)
              | cuff k l=>simpa [paiB,Lake,αG,αF,pair,cyc,Chip.budget2] using! hz -- tune
              | creel t k l=>simpa [paiB,Lake,αG,αM,pair,cyc,Chip.budget2] using! hz
 | cuff i j=> cases b with
              | litt _ _=>simpa [paiB,Lake,αG,αF,pair,cyc,Chip.budget2] using! hz
              | creel _ _ _=>simpa [paiB,Lake,αF,αM,pair,cyc,Chip.budget2] using! hz
              | cuff k l=>rw [Lake,Lake,ΨF]; exact (((H i l v.1 s.2).threes (F k j s.1 v.2)).sore).mono P hu
 | creel f i j=> cases b with
                 | litt _ _=>simpa [paiB,Lake,αG,αM,pair,cyc,Chip.budget2] using! hz
                 | cuff _ _=>simpa [paiB,Lake,αF,αM,pair,cyc,Chip.budget2] using! hz
                 | creel b k l=> rw [Lake,Lake,ΨM]; exact ((((H i l v.2.1 s.2.2).threes (F k j s.2.1 v.2.2)).sore).threes (G f b v.1 s.1)).mono U hu
-- triangle. b=grade4 or lower.Not Mixed
abbrev prideD (z x y:E4)(a b c:Book):= prism z x y a b c
lemma tryst {C:ℝ}(p:Captain t z x m C)(h:Captain t z y m C)(w:Captain t x y m C)(q:1≤ C)(ht:0<t)(a b c:Chip)(u:a.nox=true)(v:Berth z a)(r:Berth x b)(s:Berth y c): Rally (cashF C) (t^(m+1)) (Chip.budget3 (gT t) (fT t) a b c) (prism (mount t z) (mount t x) (mount t y) (Lake t m z a) (Lake t m x b) (Lake t m y c)):=by
 have hn:= pow_nonneg ht.le (m+1); rcases sizeK C q with ⟨_,_,_,X,P,B,A⟩; have hz:Rally (cashF C) (t^(m+1)) 0 0:= Rally.zero _ _ (by unfold cashF; positivity) hn; rcases p with ⟨G1,H1,F1⟩; rcases h with ⟨G2,H2,F2⟩; rcases w with ⟨G3,H3,F3⟩
 cases a with
 | litt i j=>
   cases b with
   | litt k l=>
     cases c with
     | litt u yK=>
       rw [Lake,Lake,Lake,LTla]
       have g11:=G1 i k v.1 r.1; have g12:=G1 j k v.2 r.1; have g13:=G1 i l v.1 r.2; have g14:=G1 j l v.2 r.2
       have g21:=G2 i u v.1 s.1; have g22:=G2 j u v.2 s.1; have g23:=G2 i yK v.1 s.2; have g24:=G2 j yK v.2 s.2
       have g31:=G3 k u r.1 s.1; have g32:=G3 l u r.2 s.1; have g33:=G3 k yK r.1 s.2; have g34:=G3 l yK r.2 s.2
       exact (((((g11.threes ((g22.threes g34).twice (g24.threes g32))).twice (g13.threes ((g22.threes g33).twice (g24.threes g31)))).twice (g21.threes ((g12.threes g34).twice (g14.threes g33)))).twice (g23.threes ((g12.threes g32).twice (g14.threes g31)))).mono X hn)
     | _=> simpa [Lake,prism,Chip.budget3,tri,αG,αF,αM] using! hz
   | cuff r l=> cases c <;> simpa [Lake, prism,Chip.budget3,tri,αG,αF,αM] using! hz
   | creel l k K=>
      cases c with
      | creel jM a y=>
         rw [Lake,Lake,Lake,AXla]; exact (((((H3 k y r.2.1 s.2.2).threes (F3 a K s.2.1 r.2.2)).sore).threes (((G1 i l v.1 r.1).threes (G2 j jM v.2 s.1)).twice ((G2 i jM v.1 s.1).threes (G1 j l v.2 r.1)))).mono A hn)
      | _=> simpa [Lake,prism,Chip.budget3,tri,αM,αF,αG] using! hz
 | cuff i j=>
   cases b with
   | litt _ _ => cases c <;> simpa [Lake,prism,Chip.budget3,tri,αG,αF,αM] using! hz
   | cuff k l=>
     cases c with
     | cuff u d=> rw [Lake,Lake,Lake, LFla]; exact (((((H1 i l v.1 r.2).threes (H3 k d r.1 s.2)).threes (F2 u j s.1 v.2)).twice (((H2 i d v.1 s.2).threes (F3 u l s.1 r.2)).threes (F1 k j r.1 v.2))).mono P hn)
     | _=> simpa [Lake,prism,Chip.budget3,tri,αG,αF,αM] using! hz
   | creel g k l=>
     cases c with
     | creel f u d=> rw [Lake,Lake,Lake, LXla]; exact ((((((H1 i l v.1 r.2.2).threes (H3 k d r.2.1 s.2.2)).threes (F2 u j s.2.1 v.2)).twice (((H2 i d v.1 s.2.2).threes (F3 u l s.2.1 r.2.2)).threes (F1 k j r.2.1 v.2))).threes (G3 g f r.1 s.1)).mono B hn)
     | _=> simpa [Lake,prism,Chip.budget3,tri,αG,αF,αM] using! hz
 | creel _ _ _=> contradiction
end YM.GaugeFieldConstruction.Wick.Yacht
end

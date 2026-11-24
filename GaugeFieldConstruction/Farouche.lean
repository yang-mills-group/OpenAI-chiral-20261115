import GaugeFieldConstruction.Grasped
set_option autoImplicit false
set_option maxHeartbeats 120000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
-- Tabulated rules Book. six bindings.
lemma yin (a b:FW)(x y:E4): eye (y-x) (yarn true a b)= -eye (x-y) (yarn false b a):=by
 have h:yarn true=(yarn false).flip.compr₂ (-Gap.opp):= equalsB (fun ⟨u,s⟩ ⟨v,t⟩=>by
    change yarn true _ _= -opp (yarn false (ket _) (ket _)); unfold yarn matchUp; rw [on_ket,on_ket,on_ket,on_ket]; change (if s=t then directed true _ _ else _)= -(opp (if t=s then directed false _ _ else _)); by_cases h:s=t <;> simp only [h,↓reduceIte]; · exact revD ..
    rw [if_neg (Ne.symm h)]; simp)
 rw [h]; change eye _ (-(opp (yarn false b a)))= _; rw [map_neg,Gap.reverse,neg_sub]
def αG (a b:PW):Book:= (0,times' a b,0,0)
def αF (a b:FW):Book:= (0,0,times' a b,0)
def αM (c:PW)(a b: FW):Book:= (0,0,0,times' (times' a b) c)
abbrev paiB(x y:E4)(a b:Book):=eye (y-x) (Wick.pair a b)
local notation "L" a:max b:max i:max j:max => eye (b-a) (ge i j)
local notation "μ" a:max b:max i:max j:max => eye (b-a) (yarn false i j)
variable (z x y:E4)
lemma ΨP (a b c d:PW): paiB x y (αG a b) (αG c d)= L x y a c*L x y b d+ L x y a d*L x y b c:=by
 change eye _ (cyc _ _) = _; unfold cyc αG; simp [gauge_contract]
lemma ΨF(a b c d:FW): paiB x y (αF a b) (αF c d)= -(μ x y a d*μ y x c b):=by change eye _ (cyc _ _)=_; unfold cyc αF; simp [f_pay,tick,yin]
lemma ΨM(a b:PW)(i j k l:FW): paiB x y (αM a i j) (αM b k l)= -(μ x y i l*μ y x k j)* L x y a b:=by change eye _ (cyc _ _)=_; unfold cyc αM; simp [x_pay,f_pay,tick,yin]
abbrev RunG (a b c d u v:PW):ℂ:= L z x a c*(L z y b u*L x y d v+L z y b v*L x y d u)+L z x a d*(L z y b u* L x y c v+L z y b v* L x y c u)+L z y a u*(L z x b c*L x y d v+L z x b d*L x y c v)+L z y a v*(L z x b c*L x y d u+L z x b d*L x y c u)
abbrev RunF (a b c d u v:FW):ℂ:= μ z x a d*μ x y c v*μ y z u b+ μ z y a v* μ y x u d * μ x z c b
abbrev GE0 (x y :E4):= solos ge x y
lemma Gall (a b c d u v:PW): go z x y (times' a b) (times' c d) (times' u v)=RunG z x y a b c d u v:=by
 let A:=FG z x y (times' a b); let B:=GE0 x y; let X:=times' u v; change lugs A B (times' c d) (X+Phys.swap _ X)+lugs B A (times' c d) (X+ Phys.swap _ X)=_
 simp only [X, map_add,Phys.swap_apply,sunny,A,overpay]; unfold RunG; simp_rw [show ∀ i j,B i j= L x y i j from fun _ _=>rfl]; ring
lemma Funn (a b c d u v:FW): fo z x y (times' a b) (times' c d) (times' u v)=RunF z x y a b c d u v:=by
 let A(t:Bool):= FF t z x y (times' a b); let B(t:Bool):=solos (yarn t) x y; change lugs (A false) (B true) (times' c d) (Phys.swap Mode (times' u v))+lugs (B false) (A true) (times' c d) (Phys.swap Mode (times' u v))=_
 simp_rw [Phys.swap_apply,sunny,A,days,sigh,show ∀ t i j,B t i j=eye (y-x) (yarn t i j) from fun _ _ _=>rfl,yin]; unfold RunF; ring -- tune signs; days.negative y.
lemma LFla (a b c d u v:FW): prism z x y (αF a b) (αF c d) (αF u v)= RunF z x y a b c d u v:=by change tri _ _ _ _ _ _=_; simp [tri,αF,Funn]
lemma LTla (a b c d u v:PW): prism z x y (αG a b) (αG c d) (αG u v)= RunG z x y a b c d u v:=by change tri _ _ _ _ _ _=_; simp [tri,αG,Gall]
lemma LXla (a b c d u v: FW)(i j:PW):prism z x y (αF a b) (αM i c d) (αM j u v)= RunF z x y a b c d u v* L x y i j:=by
 change tri _ _ _ _ _ _=_; simp [tri,αF,αM]; change lugs (fo z x y (times' a b)) (solos ge x y) (times' _ _) (times' _ _)=_; rw [sunny,Funn]; rfl
lemma AXla (a b c d:PW)(i j k l: FW):prism z x y (αG a b) (αM c i j) (αM d k l)= -(μ x y i l*μ y x k j)*(L z x a c*L z y b d + L z y a d*L z x b c):=by
 change tri _ _ _ _ _ _=_; simp [tri,αG,αM]; change lugs (solos fGap x y) (FG z x y (times' a b)) (times' _ _) (times' _ _)=_; rw [sunny,overpay]; change eye _ (fGap (times' i j) (times' k l))*_=_; rw [f_pay,tick,yin]; ring
end YM.GaugeFieldConstruction.Wick.Yacht
end

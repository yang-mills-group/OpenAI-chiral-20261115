import YM.CF.Jet.Balm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {m B:Side}{j l b n:ℕ}{e p d a w:ℝ} (H:CoinG j l b n d a w)(ha:0<a)(hw:0<w)(G:Guide B e p d)(M:Male)
def AuX(m B:Side)(e p:ℝ)(n:ℕ)(K:ℝ):Draw (backS m B e p):=⟨fun E _ _ _ V q=>∀ x∈V, TransK n (stampA ∘ q) x K ∧ ToR n (brim ∘ q) x K ∧∀ h:Bool, seek (tided h ∘ q) n x K⟩
def Tu(N:Side)(e p:ℝ)(n:ℕ)(K:ℝ):Draw (BinK N e p):=⟨fun E _ _ _ V q=>∀ x∈V, TransK n (fun i=> (q i).val.1) x K ∧ seek (fun i=>(q i).val.2.1) n x K∧ seek (fun i=>(q i).val.2.2) n x K⟩
lemma agree_test (n:ℕ)(K:ℝ)(t:1≤K)(B:Side):∃ C:ℝ,0≤C∧∀ (m:Side)(e p:ℝ), Inspired (Tu (CSide m B) e p n K) (ranK m B e p) (AuX m B e p n K) C n:=by
 obtain ⟨C,D,H⟩:= zap (X:=Bool) Finset.univ (by simp) n B t; refine ⟨C,D,fun m e p=>⟨D,fun E _ _ _ V s f g=>?_,?_⟩⟩
 · have F(x:E)(h:x∈V)(i:Index m)(z:Cue m) : CashCold (fun x=> (ranK m B e p (f x)).run i z) x n C:=by
      apply H E V s m (fun x=>(f x).val.1) (fun x b=> request m (bSplit m B (f x).val.2.1) (bSplit m B (f x).val.2.2) b) (fun _=>z) _ 1 (fun _=> {0}) i x h
      intro x hx; refine ⟨(g x hx).1,(fun i=>allows_const _ ((vote_unit _).trans_le t)),fun b k i=> ?_⟩
      cases b; exact (g x hx).2.2 (address m B i.1); exact (g x hx).2.1 _
   exact ⟨s,D,fun x hx i b=> (F x hx i b).1,fun x hx i b=> (F x hx i b).2⟩
 intro E _ _ _ V W k v w f h P t' p' x hx
 refine ⟨fun j=> ((h x (k hx)).1 j).germ ?_,fun j=>(allows_const (n:=n) x ((vote_unit (t' j)).trans_le t)).germ ?_,fun u i=>?_⟩
 · filter_upwards [w.mem_nhds hx] with i hi; exact congrArg (fun z => SU.fund (z.1.val.1 j)) (p' i hi) |>.symm
 · filter_upwards [w.mem_nhds hx] with i hi; exact congrArg (fun z => (z.2 j).val) (p' i hi)|>.symm
 cases u
 · apply ((h x (k hx)).2.1 i).germ; filter_upwards [w.mem_nhds hx] with x hx; exact congrArg (fun z=> hook z.1.val.2.1 i) (p' x hx) |>.symm
 apply ((h x (k hx)).2.2 i).germ; filter_upwards [w.mem_nhds hx] with x hx; exact congrArg (fun z=>hook z.1.val.2.2 i) (p' x hx)|>.symm
include H ha hw G
lemma spin_l(n':ℕ)(K:ℝ)(hK:1≤K):∃ C:ℝ,0≤C∧∀ m:Side,b≤(CSide m B).val→∀ M:Male,∀ i<n,∀ h:Bool, Screen ((forestB m B e p).botL) (AuX m B e p n' K) n' (fun x=>facePay j l n M m B (stampA x) (solesK h x) (tided h x) (stick 1) i) (rateK a B) C:=by
 obtain ⟨D,hD,T⟩:= ark_quota n' (zero_le_one.trans hK) B; obtain ⟨V,t,R⟩:= vw (K:=w) n' (le_trans (zero_le_one.trans hK) hD) ha H.posT
 have hw:0≤ quartzK a w:= qp _ _ hw.le
 let r:ℕ:=8*B.val; let W:=feeG r; have hp:0< W:=by unfold W feeG; positivity
 have ht:0≤V:=zero_le_one.trans t
 refine ⟨W*(V*quartzK a w),by positivity,fun m hm M i p' u=>?_⟩
 let A:=earnings (repeated j) (repeated j) l M (idrat (CSide m B)); let q:=idrat (CSide m B)
 have hx:= R q A _ (H.stock M q rfl hm)
 apply hx.leaps (Ω:=AuX m B e p n' K) (c:=(forestB m B e p).botL) (Φ:=foam _ r) (v:=W) (w:=W) (foams r (mul_pos (show 0<8 by decide) B.property) _) (beckL u i p' H G) (beck_c H G u p') (by positivity) (ratePos a ha B).le (le_of_eq (div_mul_cancel₀ _ hp.ne')) _ _ _
 · intro S x y p; let f:=foam_in (Domain m B) r S; let g:Agrees S (stampA x) (stampA y):=fun i l H=> p.1.1 i (f l) (f H); have he: cloudG q S=S:=by ext; simp [q,cloudG,filed]
   change Agrees S (stampA x) (stampA y)∧Agrees (cloudG q S) (stampA x) (stampA y)∧AgreeF S (ticketX u (i+1) n x) (ticketX u (i+1) n y)∧AgreeF (cloudG q S) (ticketX u i n x) (ticketX u i n y); rw [he]; exact ⟨g,g,local_arc u (i+1) n S x y p,local_arc u i n S x y p⟩
 · intro x y; refine ⟨y,Subtype.ext ?_⟩
   let Z:=(forestB m B e p).pool y x; change couple (stampA Z) (ticketX u i n Z) (ticketX u (i+1) n Z)=frost _ y (rollP u i n x)
   rw [fare_c H G hm _ x y i p'.le, fare_c H G hm _ x y (i+1) p']; exact gazeG H.stock H.posT hm ..
 intro E _ _ _ S h f P x k; obtain ⟨z,Z,F⟩:= P x k
 let g:= solesK u ∘ f; have he: arr n' g x K:= by
   rintro ⟨y,j⟩; by_cases p:j=1
   · subst j; exact Z y
   let h := F u (address m B y); convert h using 1; funext a; change ((tailP m B _ _ (y,j)):Ballot).val= (tided u _ (address m B y)).val; simp [tailP,capRow,p,arrayZ]
 have hb:= ber_m n (Nat.le_add_right i 1)
 have hk(k)(p:k∈Set.Icc 0 1): seek (fun i=>ark m B (stampA (f i)) (g i) (tided u (f i)) k (stick 1)) n' x D:=by
    have hv:stick (1:Row)∈ Phase.zone {(1:Row)}:= stick_in _ (mem_singleton_self _)
    exact T E m _ g _ _ z he (F u) (stick (1:Row)) hv.1 _ p (angel (roseV u (f x)) G _ hv k p)
 exact ⟨fun i=>(z i).mono hD,fun i=>(z i).mono hD,hk _ (railIn _ i p' ⟨hb,le_rfl⟩),hk _ (railIn _ i p' ⟨le_rfl,hb⟩)⟩
end YM.CF.Jet

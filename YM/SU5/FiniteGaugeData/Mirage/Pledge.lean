import YM.SU5.FiniteGaugeData.Mirage.Chestnut
import YM.SU5.FiniteGaugeData.Mirage.Retina
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
open Largo
variable {σ θ μ φ η ξ c C H:ℝ}{β d h w J K n L ℓ g r i v t:ℕ}
structure Rent where
 σ:ℝ
 μ:ℝ
 θ:ℝ
 φ:ℝ
 hσ:0<σ
 hμ:0<μ
 hθ:0<θ
 hφ:0<φ
 books (v:Rim)(h:Slab v)(M:Tulip.Male): Ream (shineF (stairF 4 v M)) σ θ
 seat (M:Tulip.Male): Ream (bar 4 M.val) μ φ
private lemma prestige: Nonempty Rent:=by obtain ⟨σ,θ,p,g,v⟩:=dairy; obtain ⟨μ,φ,q,b,x⟩:=pull_bar; exact ⟨σ,μ,θ,φ,p,q,g,b,v,x⟩ -- Tune.
def PlanR:= Classical.choice prestige
abbrev GaugeM(v p d J:ℕ):ℕ:= v+p+d+J+10 -- Xx coordinate radius. uses p maybe normal; set R bound tang+ (unused). adjust. price lemma below.
abbrev paperP(r d:ℕ):ℕ:= 2*(r+d)+2
def page(v:ℕ):ℕ:= 2*v+2
abbrev brush(p d J:ℕ):ℕ:= p+d+J+10
abbrev boardθ (r d J:ℕ):= brush (paperP r d) d J
abbrev boardU(v d J:ℕ):= brush (page v) d J -- require cap. using L*g≥.
def Deed(v r d J:ℕ):Axis→ℕ:=fun i=> if i=3 then 2*boardθ r d J else 2*boardU v d J
abbrev banknote(g:ℕ)(D:Axis→ℕ):ℝ:= (∏ i:Axis,(4:ℕ)*(D i+g):ℕ)
lemma wedged(K:Calibration)(D:Axis→ℕ):banknote (addgap K) D=capR K D:=rfl
-- costs ≤ζ P_nat Infl cuboid. e.g. assume r,g,J fixed, all ≤d and board; Bound exact coefficient (too large ok choose rank next). alpha≥ ; cap(Vcharge convert N'=24*k). Distinct. choose rank γ*n. 
abbrev KeyPay:ℕ:=256*(2048^3)
lemma θ_board (p:r≤d)(q:g≤d)(s:J≤d)(h:1≤d)(e:d+J+g+10≤v)(t:v>0): banknote g (Deed (24*v) r d J)≤ (v:ℝ)^3 * (d:ℝ) * KeyPay:=by
 let Vκ:=24*v; let A:=2*boardθ r d J+g; let B:=2*boardU Vκ d J+g
 have hp:4*A ≤ 256*d:=by unfold A boardθ brush paperP; omega
 have hx:4*B ≤ 2048*v:=by unfold B boardU page brush Vκ; omega
 unfold banknote; rw [show ∏ i:Axis,4*(Deed (24*v) r d J i+g)= (4*A)*(4*B)^3 from ?_]
 · have he: (4*A)*(4*B)^3 ≤ (256*d)*(2048*v)^3:=by gcongr
   unfold KeyPay; exact_mod_cast le_trans he (le_of_eq (by ring))
 rw [foldBigP]; have he(a:Tang): Deed Vκ r d J a.castSucc= _:= if_neg (show (_:Axis)≠3 from ?_); swap; · exact Fin.castSucc_ne_last a
 change (∏ i:Tang, 4*(Deed Vκ r d J i.castSucc+g))*(4*(Deed Vκ r d J 3+g))= _ -- assoc wrong
 simp_rw [he]; rw [prod_const,card_univ,show Fintype.card Tang=3 from card_fin _, Deed,if_pos rfl]; unfold A B; ring
variable (P:Rent)
abbrev cellarCost (P:Rent)(U d:ℕ):ℝ:= artE P.σ P.θ P.μ P.φ U d
private lemma calcLog (f:ℝ)(p:0≤f)(u k:ℕ): let G(v k:ℕ):= Mirage.twinCost f (v^3*k); G (24*k) u * G (24*k) u = Real.exp ((2*(24^3)*(u:ℝ)*45*4*Real.log (1+f))*(k:ℝ)^3):=by
 intro G; unfold G Mirage.twinCost; have ht:0<1+f:=add_pos_of_pos_of_nonneg one_pos p
 rw [← Real.exp_log ht, ←Real.exp_nat_mul, ←Real.exp_add]; push_cast; rw [Real.log_exp]; ring_nf -- tune
section cost
private lemma subsume (p:η≥0)(t:0≤ C)(vH:0<v)(A:ℕ) (k d g J U t':ℕ)
 (ha:1≤ k)(hβ:1 ≤A)(hg:d=A*t')(x:η*t'*KeyPay+1≤ (((v:ℕ):ℝ)/2))(u:banknote g (Deed (24*k) r d J) ≤ (k:ℝ)^3*d*KeyPay)(s:2*(24^3)*(U:ℝ)*45*4*Real.log (1+C)+2≤(A:ℝ)):
 let G:= Mirage.twinCost C ((24*k)^3*U); lighting (k^3*v) A (G*G)*Real.exp (η*banknote g (Deed (24*k) r d J))<1/4:=by
 intro G; have ht:(k:ℝ)≥1:= Nat.one_le_cast.mpr ha; let a:ℝ:=(k:ℝ)^3; have hy:1≤ a:= one_le_pow₀ ht -- need n binder
 rw [calcLog C t U k, lighting, ←Real.exp_add,←Real.exp_add]; refine lt_of_le_of_lt (Real.exp_monotone (show _ ≤ -(2:ℝ) from ?_)) ?_
 · have he: η * banknote g (Deed (24*k) r d J) ≤ η*t'*KeyPay*a*A:= (mul_le_mul_of_nonneg_left u p).trans_eq (by unfold a; rw [hg]; push_cast; ring)
   rw [Nat.cast_mul, Nat.cast_pow]; let L:=2*((24:ℝ)^3)*(U:ℝ)*45*4*Real.log (1+C); change -(A:ℝ)/2 * (a*(v:ℝ)) + L*a + η*banknote g (Deed (24*k) r d J) ≤ -2
   have hv: -(A:ℝ)/2*v + η*t'*KeyPay*A ≤ -(A:ℝ):= by
      calc
        _ ≤ -(A:ℝ)/2*v + ((v:ℝ)/2-1)*A:= by gcongr; linarith only [x]
        _ = _:=by ring
   calc
    _ ≤ -(A:ℝ)/2 * (a*(v:ℝ))+L*a + _:= add_le_add_right he _
    _ = (-(A:ℝ)/2*v+η*t'*KeyPay*A+L)*a:=by ring
    _ ≤ (-2:ℝ)*a := mul_le_mul_of_nonneg_right (by change L+2≤(A:ℝ) at s; linarith only [hv,s]) (by linarith only [hy])
    _ ≤ _:=by linarith only [hy]
 have he:4<Real.exp 2:=by rw [show (2:ℝ)=1+1 from (by norm_num),Real.exp_add]; nlinarith only [Real.exp_one_gt_d9]
 rw [Real.exp_neg,←one_div]; exact one_div_lt_one_div_of_lt (by norm_num) he
end cost
variable (η c C) (L J g :ℕ)
-- for physical L-floor placement specify ℓ height Lower half of all. l' ≥L+Ult; ensure separation in both. `N=k_val*24`. width d used for BOTH locality and plate transportation. charge witness projector `T` uses w=d. `kK` dancer poser. cutoff film p legacy height.Story.
structure DemandR (n l u l' w U r d k K A:ℕ)(t h:ℝ) : Prop where
 lv : l = L -- bottom chosen already
 tune : l+u ≤ l' -- leaves physical gap 1; strictly if needed?
 finance1: u ≤ U
 finance2: w ≤ U
 high : l'+w ≤ r
 scale : 1≤ k
 rank_n : n>0
 clock : A≥1
 delta : h≥0
 aperture : 0<t
 hot : h+tailCost c C d ≤ Real.exp (-(A:ℝ))
 buy : 2*cellarCost P U d+(2*tailCost c C d+t*C) ≤ h-tailCost c C d
 price : let G:= Mirage.twinCost (U:ℝ) ((24*k)^3*U); lighting (k^3*n) A (G*G)*Real.exp (η*banknote g (Deed (24*k) r d J))<1/4
 spare : r+d+d+(r+d+d)<24*k
 work : ∀ N:Side, N.val=24*k→∀ M:Tulip.Male, K≤ M.val.val →∀ X:Side,N.val≤X.val →
    Suite (k^3*n) X M (LodgeP d N.val (r+d)) (Opera l u N.val false) (Opera l u N.val true) U ((1+P.θ)*U) (cellarCost P U d) ∧
    Suite (k^3*n) X M (LodgeP d N.val (r+d)) (Opera l' w N.val true) (Opera l' w N.val false) U ((1+P.θ)*U) (cellarCost P U d) -- X free replace proper ∀ X≥. Both.
-- existence BuildBox. upper.I Escort µ choose Loft before α. 
variable (u0:0<c)(p0:0≤η)(v0:0 < C)
include u0 p0 v0
lemma authorize : ∃ n l u l' w U r d k K A t h, DemandR η c C P L J g n l u l' w U r d k K A t h:=by
 -- Step0 Uniform σ & c rates enable choose proportion d:T*A
 let X:= min P.σ (min P.μ (c/2)); have hx:0<X:=lt_min P.hσ (lt_min P.hμ (half_pos u0)); obtain ⟨T,Y⟩:=exists_nat_gt (2/X); have hT:0<T:= Nat.cast_pos.mp ((by positivity : 0<2/X).trans Y) -- simplify
 have hm:T≥1:=hT
 have ht(a:ℝ)(u:X≤ a): 2 ≤ a*T:= le_trans ((div_lt_iff₀ hx).1 Y).le (by rw [mul_comm]; gcongr)
 obtain ⟨n,v⟩:= exists_nat_gt ((η*T*KeyPay+1)*2); have hn:1≤ n:=by apply Nat.cast_pos.mp (lt_of_le_of_lt (a:=0) _ v); positivity
 -- l and second l' separated by at least one offset.
 obtain ⟨u,HU⟩:= purchaseN L (2*n) false; let l':= L+u+1; obtain ⟨w,HW⟩:=purchaseN l' (2*n) true; let U:=u+w; let r:= l'+ w; have hu:L+u ≤ l':=by unfold l'; omega
 -- abund used.Height precision pay choose Nat.
 let f(A:ℕ):=Real.exp (-(A:ℝ)); have hf:Tendsto f atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
 let ρ:= P.σ; let μ:=P.μ; let φ:= P.φ; let θ:= P.θ
 have hq:0 < φ:= P.hφ; have hy:0 < θ:=P.hθ
 let Rκ:= θ*U+2*φ*((1+θ)*U); have ht':0 ≤ Rκ:= add_nonneg (mul_nonneg hy.le (Nat.cast_nonneg _)) (mul_nonneg (by positivity) (by positivity));
 let tip(A:ℕ):= f A / 2; have hv(a:ℕ) : tip a>0:=half_pos (Real.exp_pos _); have hp: 0<C*4 + Rκ*4 + 4:=by linarith only [v0,ht'];
 let e:= 1/(C*24+Rκ*24+24); have hE:0<e:=by unfold e; positivity
 obtain ⟨a,h⟩:= exists_nat_gt (2*(24^3)*(U:ℝ)*45*4*Real.log (1+(U:ℝ))+2);
 obtain ⟨A,HE,hA⟩:= ((hf.eventually (ge_mem_nhds hE)).and (eventually_ge_atTop (a+r+g+J+1 :ℕ))).exists
 let d:= A*T; have ha:A≤d:=Nat.le_mul_of_pos_right _ hT; have hD(a':ℝ)(v:a'≥X): Real.exp (-a'*d)≤ f A*f A:=by rw [←Real.exp_add]; apply Real.exp_monotone; unfold d; rw [Nat.cast_mul]; nlinarith only [mul_le_mul_of_nonneg_left (ht a' v) (show 0≤(A:ℝ) by positivity)]
 let δ:= tailCost c C d; have hδ:δ ≤ f A*f A * C:= mul_le_mul_of_nonneg_right (show Real.exp _ ≤ _ from (by rw [neg_div]; exact hD (c/2) ((min_le_right ..).trans (min_le_right ..)))) v0.le
 have ht'': f A * (C*24+Rκ*24+24) ≤ 1:= (le_div_iff₀ (by positivity)).1 HE; have hF:0 < f A:=Real.exp_pos _
 have hα:δ ≤ tip A /6:= hδ.trans (by
    unfold tip; rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (show f A*C ≤ 1/12 from (by nlinarith only [ht'',mul_nonneg hF.le v0.le,mul_nonneg hF.le ht',hF,hE])) hF.le).trans (le_of_eq (by ring)))
 let t:= tip A / (4*C); have hK:t*C= tip A/4:=by unfold t; field_simp
 have hyc:cellarCost P U d ≤ f A*f A*Rκ:= by
    let V:= f A*f A; unfold cellarCost artE; unfold Rκ; change Real.exp (-ρ*d)*θ*U+2*(Real.exp (-μ*d)*φ)*((1+θ)*U) ≤ _
    calc
      _ ≤ V*θ*U+2*(V*φ)*((1+θ)*U):= (by gcongr; exact hD ρ (min_le_left ..); exact hD μ ((min_le_right ..).trans (min_le_left ..)))
      _ = _:= by unfold V; ring
 have hβ: 2*cellarCost P U d ≤ tip A/6:=by
    have he:f A *Rκ≤ 1/24:= by nlinarith only [ht'',mul_nonneg hF.le v0.le,mul_nonneg hF.le ht',hF]
    unfold tip; nlinarith only [mul_le_mul_of_nonneg_left he hF.le,hF,hyc]
 obtain ⟨b,hb⟩:= enchant d r n hn
 let k:= b+r+d+d+d+J+g+10+U+1; have hk: r+d+d+(r+d+d)<24*k:=by unfold k; omega
 refine ⟨n,L,u,l',w,U,r,d,k,U,A,t,tip A, ?_,hu,?_,?_,le_rfl,?_,hn,by omega,(hv A).le,?_, ?_,?_, ?_, hk,?_⟩
 · rfl
 · unfold U; omega
 · unfold U; omega
 · unfold k; omega
 · unfold t; exact div_pos (hv A) (by positivity)
 · change tip A+δ ≤ f A; unfold tip at *; linarith only [hα,hF]
 · change _+(2*δ+ t*C) ≤ tip A - δ; linarith only [hα,hβ,hK,hv A]
 · intro hG; exact subsume p0 (by positivity) hn A k d g J U T (by unfold k; omega) (by omega) rfl (le_of_lt ((lt_div_iff₀ (by norm_num)).2 v)) (θ_board (by omega) (by omega) (by omega) (by omega) (by unfold k; omega) (by unfold k; omega)) (h.le.trans (Nat.cast_le.mpr (by omega)))
 intro N HH M P0 S t; let V:= Curtain.platter N k; have he:Even N.val:=by rw [HH]; exact (even_iff_two_dvd.mpr ⟨12*k,by ring⟩)
 let T:=commissioned (μ:=P.μ) (σ:=P.σ) (K:=P.φ) (ζ:=P.θ) (l:=L) (l':=l') (r:=r) (n:=2*n) (u:=u) (w:=w) (d:=d) (m:=k^3*n) (P.seat M) P.hσ P.hθ P.hμ hq.le (fun i t=> P.books _ (Curtain.platterA HH i t) M) (HH.symm ▸ hk) HH t (hu.trans (by unfold r; omega)) le_rfl
 obtain ⟨u',w'⟩:= T (fun i=>HU M.val N (by unfold U at P0; omega) M.property (by unfold k U at HH; omega) he _ (Curtain.platterA HH _ i.property)) (fun i=>HW M.val N (by unfold U at P0; omega) M.property (by unfold k U at HH; omega) he _ (Curtain.platterA HH _ i.property)) (HH.symm ▸ hb k (by unfold k; omega))
 -- costs.V.Clock. adjust.
 have he(S' x y : Finset Cover)(d' :ℕ)(U₀: d'≤U)(X:Suite (k^3*n) S M S' x y d' ((1+θ)*d') (cellarCost P d' d)): Suite (k^3*n) S M S' x y U ((1+θ)*U) (cellarCost P U d):=by
    obtain ⟨A,X,B,q,v⟩:= X.choice; refine ⟨_,_,_,q.bill' (Nat.cast_le.mpr U₀) ?_ ?_,v⟩; · gcongr
    exact artE_mono hy.le hq.le U₀
 exact ⟨he _ _ _ u (Nat.le_add_right ..) u', he _ _ _ w (Nat.le_add_left ..) w'⟩
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest

import YM.CF.Cascade.Doric
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
section comp
variable {D E B:Type*}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]
lemma trim_p {N:ℕ}(f g:D→E)(t:E×D→ B)(p:ContDiffAt ℝ N f 0)(q:ContDiffAt ℝ N g 0)(u:ContDiffAt ℝ N t (g 0,0))(v:cFoot (N+1) (f-g)): cFoot (N+1) (fun d => t (f d,d)-t (g d,d)) ∧ f 0=g 0∧ ContDiffAt ℝ N (fun d=>t (f d,d)) 0∧ ContDiffAt ℝ N (fun d=>t (g d,d)) 0:=by
 have hp(i:ℕ)(h:i≤N):iteratedFDeriv ℝ i f 0= iteratedFDeriv ℝ i g 0:=by rw [←sub_eq_zero, ← iteratedFDeriv_sub_apply (p.of_le (by exact_mod_cast h)) (q.of_le (by exact_mod_cast h))]; exact v i (by omega)
 have hw:f 0=g 0:=by have hx:=hp 0 (Nat.zero_le _); exact (show _= (iteratedFDeriv ℝ 0 f 0) 0 from (iteratedFDeriv_zero_apply _).symm).trans ((DFunLike.congr_fun hx 0).trans (iteratedFDeriv_zero_apply ..))
 let F(d:D):=(f d,d); let G(d:D):=(g d,d); have hm:F 0=G 0:=Prod.ext hw rfl
 have hF:ContDiffAt ℝ N F 0:= p.prodMk contDiffAt_id; have hG:ContDiffAt ℝ N G 0:=q.prodMk contDiffAt_id; have hY:ContDiffAt ℝ N t (F 0):=by rw [hm]; exact u
 let H:=t∘ F; let P:=t∘ G; have he:ContDiffAt ℝ N H 0:=hY.comp 0 hF; have hx:ContDiffAt ℝ N P 0:=u.comp (g:=t) (f:=G) 0 hG
 have hv(i:ℕ)(h:i≤N):iteratedFDeriv ℝ i F 0=iteratedFDeriv ℝ i G 0:=by unfold F G; rw [iteratedFDeriv_prodMk p (show ContDiffAt ℝ N (fun x:D=>x) 0 from contDiffAt_id) (by exact_mod_cast h), iteratedFDeriv_prodMk q (show ContDiffAt ℝ N (fun x:D=>x) 0 from contDiffAt_id) (by exact_mod_cast h),hp i h] -- contDiffAt_id'?
 refine ⟨fun i h=>?_,hw,he,hx⟩; change iteratedFDeriv ℝ i (H-P) _=_; have hh:(i:WithTop ℕ∞) ≤ (N:WithTop ℕ∞):=by exact_mod_cast (show i≤N by omega)
 rw [iteratedFDeriv_sub_apply (he.of_le hh) (hx.of_le hh),sub_eq_zero]; unfold H P; rw [iteratedFDeriv_comp hY hF hh,iteratedFDeriv_comp (show ContDiffAt ℝ N t (G 0) from u) hG hh, hm]; unfold FormalMultilinearSeries.taylorComp; refine sum_congr rfl fun x _=>?_ ; ext1 y; change (iteratedFDeriv ℝ x.length t (G 0)) _=(iteratedFDeriv ℝ x.length t (G 0)) _; congr 1; ext1 j; change (iteratedFDeriv ℝ (x.partSize j) F 0) _= _; rw [hv (x.partSize j) ((x.partSize_le j).trans (by omega))]; rfl
lemma trim_addI {D E:Type*}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup E][NormedSpace ℝ E]{f g:D→E}(p:ContDiffAt ℝ t f 0)(q:ContDiffAt ℝ t g 0): trim t (f+g)=trim t f+trim t g:=by funext x; unfold trim cake; rw [iteratedFDeriv_add_apply p q, smul_add]; rfl
lemma lushZ {D E:Type*}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup E][NormedSpace ℝ E]{f g:D→E}(p:ContDiffAt ℝ t f 0)(q:ContDiffAt ℝ t g 0)(h:cFoot (t+1) (f-g)):trim t f=trim t g:=by funext x; have hx:= h t (by omega); rw [iteratedFDeriv_sub_apply p q,sub_eq_zero] at hx; unfold trim cake; rw [hx]
end comp
lemma voye (x: Site (More n)→ℂ) (H:ContDiffAt ℝ ω (spar j M (N:=n)∘ represent) 0){U:Dress n}(v:Ample U){P:Cloud n→Op (Single n)}(g:ContDiffAt ℝ ω P 0)(p:cFoot 3 (P-Crops j M U ∘ represent))(h: Foot (ting (0:CoreX)) j M.val (ArcJ 0 j M U)) :let V:=fun u:Cloud n=> OrbT (tickA n) (spar j M (represent u)) (P u); ContDiffAt ℝ (↑(2:ℕ)) V 0∧ trim 2 V=trim 2 (gala M j U ∘ represent):=by
 intro V; let K:=(spar j M ∘ represent (n:=More n)); let B':= Crops j M U ∘ represent; let W(p:Op (Single n)× Cloud n):=OrbT (tickA n) (K p.2) p.1
 have hp:= heat_n n _ (hourZ U M 0 h); let Q:Op (Single n)× Cloud n→ Op (Single n):= fun p=>tickA n*(1+p.1)* K p.2; have hQ: Q (B' 0,0)= grace j M U 0:=rfl; have hu: ContDiffAt ℝ ω W (B' 0,0):=by
    rw [show W= foray n ∘ Q from funext fun i=> (beamCash ..).symm]; refine ContDiffAt.comp (g:=foray n) (f:=Q) _ (hQ.symm ▸ hp) ?_; exact ((ContDiffAt.mul contDiffAt_const (contDiffAt_const.add contDiffAt_fst)).mul (H.comp (g:=K) (f:=Prod.snd) _ contDiffAt_snd))
 have hB : ContDiffAt ℝ ω B' 0:= (((contDiffAt_const.sub H).mul v.self.2).mul H)
 obtain ⟨hT,-,ht,hp'⟩:= trim_p (N:=2) P B' W (g.of_le le_top) (hB.of_le le_top) (hu.of_le le_top) p
 exact ⟨ht,lushZ ht hp' hT⟩
variable (H:Hull j L ho a b d e t m X B G T F z Y P)(M: Male)
include H
lemma taxMove (U:Dress (CSide X B))(W:Dress (CSide m B))(U':ContDiffAt ℝ ω (spar j M (N:= CSide X B) ∘ represent) 0)(U0:Ample U)(Q: ContDiffAt ℝ ω (spar j (upMale L ho M) (N:=CSide m B) ∘ represent) 0)(W':Ample W)(h:cFoot 3 (emergence L j ho G F z M U-flareP L j ho M W)) (c:ContDiffAt ℝ (↑(2:ℕ)) (deflate (lush G P M U∘ ears F z)) 0) :trim 2 (fun x:Vox m B=> gala M j U (baby F z x))=Complex.reCLM ∘ trim 2 (deflate (lush G P M U∘ ears F z))+ trim 2 (gala (upMale L ho M) j W∘ represent):=by
 let P':=G; let C':= CSide m B; let V:=upMale L ho M; let Y:=emergence L j ho G F z M U; let t:=lush G P M U ∘ ears F z
 have hp:= voye (n:=C') 0 Q W' (H.terms M U0.self).2.2.2 h (Grace 0 H.hi H.above H.stamp V H.size_p W W' Q)
 let g(x:Vox m B):= OrbT (tickA C') (spar j V (represent x)) (Y x); let f:= Complex.reCLM∘ t
 have hx : ContDiffAt ℝ (↑(2:ℕ)) t 0:=by rw [show t=deflate t+ (fun _=>t 0) from funext fun i=> (sub_add_cancel (t i) (t 0)).symm]; exact c.add contDiffAt_const
 have hf:ContDiffAt ℝ (↑(2:ℕ)) f 0:= Complex.reCLM.contDiff.contDiffAt.comp _ hx
 have he:= shear U H U0 M U'; rw [← show trim 2 g = _ from hp.2]; unfold trim cake; rw [show iteratedFDeriv ℝ 2 (fun x=>gala M j U (baby F z x)) 0= iteratedFDeriv ℝ 2 (f+g) 0 from ((show _=ᶠ[𝓝 0] f+g from he).iteratedFDeriv ℝ 2).eq_of_nhds]; change trim 2 (f+g)=_; rw [trim_addI hf hp.1]; funext x; change trim 2 f x+_=Complex.reCLM (trim 2 (deflate t) x)+_; congr 1; change trim 2 f _= _; rw [show trim 2 (deflate t) x=trim 2 t x from ?_]; exact extendJ _ _ _ _ hx le_rfl _; unfold trim; rw [cake_p hx (by omega)]
end YM.CF.Cascade

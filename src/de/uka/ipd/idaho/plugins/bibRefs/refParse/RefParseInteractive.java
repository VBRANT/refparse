/* RefParse, the algorithm for parsing lists of bibliographic references.
 * Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package de.uka.ipd.idaho.plugins.bibRefs.refParse;

import java.util.Properties;

import de.uka.ipd.idaho.gamta.MutableAnnotation;
import de.uka.ipd.idaho.gamta.util.AnnotationFilter;
import de.uka.ipd.idaho.gamta.util.ProgressMonitor;
import de.uka.ipd.idaho.gamta.util.ProgressMonitor.CascadingProgressMonitor;
import de.uka.ipd.idaho.plugins.bibRefs.refParse.RefParse.AuthorListStyle;

/**
 * @author sautter
 *
 */
public class RefParseInteractive extends RefParseAnalyzer {
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.plugins.bibRefs.refParse.RefParseAnalyzer#processBibRefs(de.uka.ipd.idaho.gamta.MutableAnnotation, de.uka.ipd.idaho.gamta.MutableAnnotation[], java.util.Properties, de.uka.ipd.idaho.gamta.util.ProgressMonitor)
	 */
	protected void processBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefs, Properties parameters, ProgressMonitor pm) {
		this.processBibRefs(data, bibRefs, parameters, null, false, pm);
	}
	private void processBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefs, Properties parameters, AuthorListStyle als, boolean isRecursiveCall, ProgressMonitor pm) {
		
		//	parse references
		pm.setStep("Parsing references");
		pm.setBaseProgress(0);
		pm.setMaxProgress(80);
		als = this.refParse.parseBibRefs(data, bibRefs, parameters, als, new CascadingProgressMonitor(pm));
		
		//	cannot get feedback, we're done here
		if (!parameters.containsKey(INTERACTIVE_PARAMETER))
			return;
		
		//	get feedback
		pm.setStep("Getting feedback");
		pm.setBaseProgress(80);
		pm.setMaxProgress(90);
		MutableAnnotation[] splitBibRefs = this.refParse.getFeedback(data, bibRefs, true, true, pm);
		
		//	recurse with split references (if any)
		if (splitBibRefs != null)
			this.processBibRefs(data, splitBibRefs, parameters, als, true, pm);
		
		//	we are in a recursive call, so we're done
		if (isRecursiveCall)
			return;
		
		//	refresh references in case we had a split or removal
		bibRefs = data.getMutableAnnotations(BIBLIOGRAPHIC_REFERENCE_TYPE);
		
		//	truncate leading and tailing punctuation from detail annotations
		pm.setStep("Trimming detail punctuation");
		pm.setBaseProgress(90);
		pm.setMaxProgress(95);
		this.refParse.trimPunctuation(bibRefs, pm);
		
		//	add detail attributes (and learn along the way)
		pm.setStep("Setting detail attributes");
		pm.setBaseProgress(95);
		pm.setMaxProgress(100);
		this.refParse.setDetailAttributes(bibRefs, pm);
		
		//	clean up feedback control attribute
		AnnotationFilter.removeAnnotationAttribute(data, BIBLIOGRAPHIC_REFERENCE_TYPE, RefParse.GOT_FEEDBACK_ATTRIBUTE);
	}
}

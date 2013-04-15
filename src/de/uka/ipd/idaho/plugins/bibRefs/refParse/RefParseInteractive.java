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
import de.uka.ipd.idaho.plugins.bibRefs.refParse.RefParse.AuthorListStyle;

/**
 * @author sautter
 *
 */
public class RefParseInteractive extends RefParseAnalyzer {
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.plugins.bibliographicReferences.RefParseAnalyzer#processBibRefs(de.uka.ipd.idaho.gamta.MutableAnnotation, de.uka.ipd.idaho.gamta.MutableAnnotation[], java.util.Properties)
	 */
	protected void processBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefs, Properties parameters) {
		this.processBibRefs(data, bibRefs, parameters, null, false);
	}
	private void processBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefs, Properties parameters, AuthorListStyle als, boolean isRecursiveCall) {
		
		//	parse references
		als = this.refParse.parseBibRefs(data, bibRefs, parameters, als);
		
		//	cannot get feedback, we're done here
		if (!parameters.containsKey(INTERACTIVE_PARAMETER))
			return;
		
		//	get feedback
		MutableAnnotation[] splitBibRefs = this.refParse.getFeedback(data, bibRefs, true, true);
		
		//	recurse with split references (if any)
		if (splitBibRefs != null)
			this.processBibRefs(data, splitBibRefs, parameters, als, true);
		
		//	we are in a recursive call, so we're done
		if (isRecursiveCall)
			return;
		
		//	refresh references in case we had a split or removal
		bibRefs = data.getMutableAnnotations(BIBLIOGRAPHIC_REFERENCE_TYPE);
		
		//	truncate leading and tailing punctuation from detail annotations
		this.refParse.trimPunctuation(bibRefs);
		
		//	add detail attributes (and learn along the way)
		this.refParse.setDetailAttributes(bibRefs);
		
		//	clean up feedback control attribute
		AnnotationFilter.removeAnnotationAttribute(data, BIBLIOGRAPHIC_REFERENCE_TYPE, RefParse.GOT_FEEDBACK_ATTRIBUTE);
	}
}
